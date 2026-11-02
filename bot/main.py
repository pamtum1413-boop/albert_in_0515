"""비트겟 USDT 선물 알림 봇 (BTC·ETH·SOL, 기본은 주문 없이 텔레그램 알림만).

GitHub Actions가 매시간 실행합니다. 규칙은 'BTC 선물 알림 전략 규칙표' 문서를 따릅니다.
- 전략 C1: 20일 터틀 돌파 + 전날 일봉 MACD 확인 (BTC, ETH)
- 전략 A: 4시간봉 추세 + 1시간봉 눌림목 + 과열 회피 (BTC, SOL)
- 코인별로 켜는 전략은 config.json 의 coins 에서 정합니다 (알트코인 분석 결과).
- 하루 한도와 포지션 1개 규칙은 모든 코인을 합쳐서 적용합니다.
- 매일 한국 시간 오전 9시 시장 방향 요약
"""
import base64
import csv
import hashlib
import hmac
import json
import math
import os
import sys
import time
import urllib.parse
import urllib.error
import urllib.request
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATE_PATH = os.path.join(ROOT, "state", "state.json")
JOURNAL_PATH = os.path.join(ROOT, "state", "journal.csv")
CONFIG_PATH = os.path.join(ROOT, "config.json")

API = "https://api.bitget.com"
SYMBOL = "BTCUSDT"  # 지금 검사 중인 코인 (main 에서 코인마다 바꿉니다)
COIN = "BTC"
DEFAULT_COINS = {"BTCUSDT": {"C1": True, "A": True}}
PRODUCT = "USDT-FUTURES"
KST = ZoneInfo("Asia/Seoul")
NY = ZoneInfo("America/New_York")
HOUR = 3600


# ---------------------------------------------------------------- 데이터

def get_json(path, params):
    url = f"{API}{path}?{urllib.parse.urlencode(params)}"
    last = None
    for attempt in range(4):
        try:
            with urllib.request.urlopen(url, timeout=20) as r:
                body = json.load(r)
            if body.get("code") != "00000":
                raise RuntimeError(f"Bitget 오류: {body.get('msg')}")
            return body["data"]
        except Exception as e:  # 네트워크 오류는 잠시 쉬고 다시 시도
            last = e
            time.sleep(2 ** attempt)
    raise last


def parse_candles(rows):
    # [시작시각(초), 시가, 고가, 저가, 종가, 거래량]
    out = {int(r[0]) // 1000: [int(r[0]) // 1000] + [float(x) for x in r[1:6]] for r in rows}
    return [out[k] for k in sorted(out)]


def candles(granularity, seconds, limit=1000):
    """마감된 봉만 돌려줍니다."""
    rows = get_json("/api/v2/mix/market/candles", dict(
        symbol=SYMBOL, productType=PRODUCT, granularity=granularity, limit=limit))
    now = time.time()
    return [c for c in parse_candles(rows) if c[0] + seconds <= now]


def daily_candles(pages=3):
    """UTC 일봉(한국 시간 오전 9시 마감). EMA200 계산을 위해 과거 봉을 넉넉히 받습니다."""
    rows, end = [], int(time.time() * 1000)
    for _ in range(pages):
        page = get_json("/api/v2/mix/market/history-candles", dict(
            symbol=SYMBOL, productType=PRODUCT, granularity="1Dutc", limit=200, endTime=end))
        if not page:
            break
        rows += page
        end = min(int(r[0]) for r in page) - 1
    now = time.time()
    return [c for c in parse_candles(rows) if c[0] + 86400 <= now]


def market_info():
    t = get_json("/api/v2/mix/market/ticker", dict(symbol=SYMBOL, productType=PRODUCT))[0]
    oi = get_json("/api/v2/mix/market/open-interest", dict(symbol=SYMBOL, productType=PRODUCT))
    try:
        ls = get_json("/api/v2/mix/market/account-long-short", dict(symbol=SYMBOL, period="1h"))
        ls_ratio = float(ls[-1]["longShortAccountRatio"])
    except Exception:
        ls_ratio = None
    try:
        ps = get_json("/api/v2/mix/market/position-long-short", dict(symbol=SYMBOL, period="1h"))
        long_share = float(ps[-1]["longPositionRatio"])
    except Exception:
        long_share = None
    return dict(
        price=float(t["lastPr"]),
        funding=float(t["fundingRate"]),
        oi=float(oi["openInterestList"][0]["size"]),
        ls_ratio=ls_ratio,
        long_share=long_share,
    )


# ---------------------------------------------------------------- 청산 지도 (추정)

# 거래소가 청산 히트맵을 공개하지 않아서, 최근 7일 1시간봉 거래량을 진입 물량으로 보고
# 흔히 쓰는 레버리지별로 청산 가격을 계산해 추정합니다. 이미 가격이 지나간 청산 가격은 뺍니다.
LEVERAGE_MIX = {10: 0.25, 20: 0.25, 25: 0.2, 50: 0.2, 100: 0.1}
MAINT_MARGIN = 0.004


def liq_bucket(price):
    """가격의 약 0.6% 폭으로 묶습니다 (BTC 8만이면 500)."""
    raw = price * 0.006
    step = 10 ** math.floor(math.log10(raw))
    return next(m * step for m in (1, 2, 5, 10) if m * step >= raw)


def liquidation_map(h1, price, long_share, hours=168, span=0.08):
    LIQ_BUCKET = liq_bucket(price)
    bars = h1[-hours:]
    n = len(bars)
    # 각 봉 이후에 나온 최저가/최고가 (그 사이에 이미 청산된 물량을 빼기 위해)
    later_low, later_high = [0.0] * n, [0.0] * n
    lo, hi = price, price
    for j in range(n - 1, -1, -1):
        later_low[j], later_high[j] = lo, hi
        lo, hi = min(lo, bars[j][3]), max(hi, bars[j][2])
    ls = long_share if long_share else 0.5
    longs, shorts = {}, {}
    for j, c in enumerate(bars):
        entry = (c[2] + c[3] + c[4]) / 3
        usdt = c[5] * entry
        for lev, w in LEVERAGE_MIX.items():
            lp = entry * (1 - 1 / lev + MAINT_MARGIN)
            sp = entry * (1 + 1 / lev - MAINT_MARGIN)
            if later_low[j] > lp and lp >= price * (1 - span):
                k = math.floor(lp / LIQ_BUCKET) * LIQ_BUCKET
                longs[k] = longs.get(k, 0) + usdt * w * ls
            if later_high[j] < sp and sp <= price * (1 + span):
                k = math.floor(sp / LIQ_BUCKET) * LIQ_BUCKET
                shorts[k] = shorts.get(k, 0) + usdt * w * (1 - ls)
    if not longs and not shorts:
        return None
    total = sum(longs.values()) + sum(shorts.values())
    top = lambda d: max(d.items(), key=lambda kv: kv[1]) if d else None
    return dict(bucket=LIQ_BUCKET, long_top=top(longs), short_top=top(shorts), long_sum=sum(longs.values()),
                short_sum=sum(shorts.values()), total=total, long_share=ls)


def liq_lines(lm, price, short=False):
    if not lm:
        return ["청산 몰린 가격대: 계산할 데이터가 부족합니다."]

    def zone(kv):
        k, v = kv
        mid = k + lm["bucket"] / 2
        return f"{fmt(k)}~{fmt(k + lm['bucket'])} (현재가 대비 {(mid / price - 1) * 100:+.1f}%, 전체의 {v / lm['total'] * 100:.0f}%)"

    up = lm["short_sum"] / lm["total"] * 100
    side = "위쪽(숏 청산)" if up >= 50 else "아래쪽(롱 청산)"
    lines = []
    if short:
        lines.append(f"청산 몰린 쪽(추정): {side} {max(up, 100 - up):.0f}%")
        if lm["short_top"]:
            lines.append(f"  위 최대: {zone(lm['short_top'])}")
        if lm["long_top"]:
            lines.append(f"  아래 최대: {zone(lm['long_top'])}")
        return lines
    lines.append("[청산 몰린 가격대 · 추정, 현재가 ±8%]")
    if lm["short_top"]:
        lines.append(f"• 위쪽 최대(숏 청산): {zone(lm['short_top'])}")
    if lm["long_top"]:
        lines.append(f"• 아래쪽 최대(롱 청산): {zone(lm['long_top'])}")
    lines.append(f"• 비중: 위쪽 {up:.0f}% / 아래쪽 {100 - up:.0f}% → {side} 물량이 더 많음")
    lines.append(f"  (포지션 비율 롱 {lm['long_share'] * 100:.0f}% 반영. 가격은 청산 물량이 많은 쪽으로 "
                 "끌려가는 경우가 많지만, 추정치라 진입 근거로는 쓰지 않습니다.)")
    return lines


# ---------------------------------------------------------------- 지표

def ema(xs, n):
    k, out = 2 / (n + 1), []
    e = xs[0]
    for x in xs:
        e = x * k + e * (1 - k)
        out.append(e)
    return out


def atr(cs, n):
    trs = [cs[0][2] - cs[0][3]]
    for i in range(1, len(cs)):
        h, l, pc = cs[i][2], cs[i][3], cs[i - 1][4]
        trs.append(max(h - l, abs(h - pc), abs(l - pc)))
    out = [None] * len(trs)
    out[n - 1] = sum(trs[:n]) / n
    for i in range(n, len(trs)):
        out[i] = (out[i - 1] * (n - 1) + trs[i]) / n
    return out


def rsi(closes, n=14):
    out = [None] * len(closes)
    gains = [max(closes[i] - closes[i - 1], 0) for i in range(1, len(closes))]
    losses = [max(closes[i - 1] - closes[i], 0) for i in range(1, len(closes))]
    ag, al = sum(gains[:n]) / n, sum(losses[:n]) / n
    for i in range(n, len(closes)):
        if i > n:
            ag = (ag * (n - 1) + gains[i - 1]) / n
            al = (al * (n - 1) + losses[i - 1]) / n
        out[i] = 100 - 100 / (1 + ag / al) if al else 100.0
    return out


def macd_hist(closes):
    m = [a - b for a, b in zip(ema(closes, 12), ema(closes, 26))]
    return [a - b for a, b in zip(m, ema(m, 9))]


def kdj(cs, n=9):
    k = d = 50.0
    ks, ds, js = [], [], []
    for i in range(len(cs)):
        win = cs[max(0, i - n + 1):i + 1]
        hh, ll = max(c[2] for c in win), min(c[3] for c in win)
        rsv = (cs[i][4] - ll) / (hh - ll) * 100 if hh > ll else 50
        k = 2 / 3 * k + rsv / 3
        d = 2 / 3 * d + k / 3
        ks.append(k)
        ds.append(d)
        js.append(3 * k - 2 * d)
    return ks, ds, js


def mfi(cs, n=14):
    tp = [(c[2] + c[3] + c[4]) / 3 for c in cs]
    out = [None] * len(cs)
    for i in range(n, len(cs)):
        pos = sum(tp[j] * cs[j][5] for j in range(i - n + 1, i + 1) if tp[j] > tp[j - 1])
        neg = sum(tp[j] * cs[j][5] for j in range(i - n + 1, i + 1) if tp[j] < tp[j - 1])
        out[i] = 100 - 100 / (1 + pos / neg) if neg else 100.0
    return out


def bollinger(closes, i, n=20):
    win = closes[i - n + 1:i + 1]
    mid = sum(win) / n
    sd = (sum((x - mid) ** 2 for x in win) / n) ** 0.5
    return mid - 2 * sd, mid, mid + 2 * sd


def trend_dir(closes):
    """종가와 EMA50/200 배열로 방향을 정합니다: 1 롱만, -1 숏만, 0 쉬어감."""
    e50, e200 = ema(closes, 50), ema(closes, 200)
    c = closes[-1]
    if c > e200[-1] and e50[-1] > e200[-1]:
        return 1, e50, e200
    if c < e200[-1] and e50[-1] < e200[-1]:
        return -1, e50, e200
    return 0, e50, e200


# ---------------------------------------------------------------- 표시

def fmt(x):
    if abs(x) >= 1000:
        return f"{x:,.0f}"
    if abs(x) >= 1:
        return f"{x:,.2f}"
    return f"{x:.4f}"


def sfmt(x):
    return ("+" if x >= 0 else "−") + fmt(abs(x))


def side_word(side):
    return "롱" if side == 1 else "숏"


def dir_word(d):
    return {1: "롱만", -1: "숏만", 0: "쉬어감 (방향 엇갈림)"}[d]


def time_tag(ts):
    """거래량 분석 결과에 따른 시간대 표시 (미국 서머타임 자동 반영)."""
    kst = datetime.fromtimestamp(ts, KST)
    ny = datetime.fromtimestamp(ts, NY)
    if kst.weekday() >= 5:
        return "주말 · 저유동성 시간 ⚠"
    if 9 <= ny.hour < 12:
        return "거래량 많은 시간 ✔"
    if 15 <= ny.hour < 20:
        return "저유동성 시간 ⚠"
    return "보통 시간"


def sizing(cfg, entry, stop):
    notional = cfg["account_usdt"] * cfg["margin_pct"] / 100 * cfg["leverage"]
    dist = abs(entry - stop) / entry
    loss = notional * dist
    return notional, dist, loss


def position_lines(cfg, entry, stop):
    notional, dist, loss = sizing(cfg, entry, stop)
    margin = notional / cfg["leverage"]
    lines = [
        f"포지션: {fmt(notional)} USDT (증거금 {fmt(margin)} USDT, {cfg['leverage']}배)",
        f"손절 시 손실: {loss:.2f} USDT (계좌의 {loss / cfg['account_usdt'] * 100:.1f}%)",
    ]
    if dist * 100 > cfg["stop_warn_pct"]:
        lines.append(f"⚠ 손절 거리 {dist * 100:.1f}%: 계좌 2% 넘게 잃을 수 있는 자리입니다. 거래소에 손절 주문을 꼭 걸어 두세요.")
    return lines


# ---------------------------------------------------------------- 상태·기록

def load_state():
    state = {}
    if os.path.exists(STATE_PATH):
        with open(STATE_PATH, encoding="utf-8") as f:
            state = json.load(f)
    coins = state.setdefault("coins", {})
    if "BTCUSDT" not in coins:  # 예전(BTC 전용) 상태 파일을 코인별 칸으로 옮깁니다.
        coins["BTCUSDT"] = {k: state.pop(k) for k in CoinState.PER if k in state}
    return state


class CoinState:
    """코인마다 따로 기억할 값(포지션, 마지막 봉 등)은 coins[코인]에, 나머지(하루 한도, 누적 성적)는 공용으로 둡니다."""
    PER = ("c1_pos", "a_pos", "a_last_bar", "c1_last_signal_day", "oi_history", "summary_day")

    def __init__(self, root, symbol):
        self.root = root
        self.own = root.setdefault("coins", {}).setdefault(symbol, {})

    def _t(self, k):
        return self.own if k in self.PER else self.root

    def get(self, k, default=None):
        return self._t(k).get(k, default)

    def __getitem__(self, k):
        return self._t(k)[k]

    def __setitem__(self, k, v):
        self._t(k)[k] = v


def open_positions(state):
    root = getattr(state, "root", state)
    return [(sym, k) for sym, c in root.get("coins", {}).items() for k in ("c1_pos", "a_pos") if c.get(k)]


def save_state(state):
    with open(STATE_PATH, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=1)


def journal(strategy, event, side, price, stop=None, tp1=None, tp2=None, pnl=None, note=""):
    new = not os.path.exists(JOURNAL_PATH)
    with open(JOURNAL_PATH, "a", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        if new:
            w.writerow(["시각(KST)", "전략", "이벤트", "방향", "가격", "손절", "1차익절", "2차익절", "손익(USDT)", "메모"])
        r = lambda x: "" if x is None else round(x, 2)
        w.writerow([datetime.now(KST).strftime("%Y-%m-%d %H:%M"), f"{COIN} {strategy}", event,
                    side_word(side) if side else "", r(price), r(stop), r(tp1), r(tp2), r(pnl), note])


# ---------------------------------------------------------------- 텔레그램

class Telegram:
    def __init__(self, state):
        self.token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
        self.chat_id = os.environ.get("TELEGRAM_CHAT_ID", "").strip() or state.get("chat_id", "")
        self.state = state

    def call(self, method, params):
        data = urllib.parse.urlencode(params).encode()
        req = urllib.request.Request(f"https://api.telegram.org/bot{self.token}/{method}", data=data)
        with urllib.request.urlopen(req, timeout=20) as r:
            return json.load(r)

    def ready(self):
        if not self.token:
            return False
        if not self.chat_id:
            # 봇에게 보낸 마지막 메시지에서 대화방 번호를 찾습니다.
            updates = self.call("getUpdates", {}).get("result", [])
            chats = [u["message"]["chat"]["id"] for u in updates if "message" in u]
            if not chats:
                print("텔레그램 봇에게 아무 메시지나 한 번 보낸 뒤 다시 실행해 주세요.")
                return False
            self.chat_id = str(chats[-1])
            self.state["chat_id"] = self.chat_id
            self.send("✅ 알림 봇이 연결됐습니다. 이제 이 대화방으로 알림을 보냅니다.")
        return True

    def send(self, text):
        if not self.token:
            print("----- (미리보기, 전송 안 함) -----\n" + text)
            return
        self.call("sendMessage", {"chat_id": self.chat_id, "text": text, "disable_web_page_preview": "true"})


# ---------------------------------------------------------------- 하루 한도

FEE_ROUND_TRIP = 0.0012  # 시장가 진입+청산 수수료 (0.06% × 2)


def day_key_kst():
    """하루는 한국 시간 오전 9시에 바뀝니다."""
    return (datetime.now(KST) - timedelta(hours=9)).strftime("%Y-%m-%d")


def day_stats(state):
    d = state.get("day")
    if not d or d.get("key") != day_key_kst():
        d = dict(key=day_key_kst(), entries=0, pnl=0.0, loss_notice=False)
        state["day"] = d
    return d


def entry_block(cfg, state):
    """새로 진입하면 안 되는 이유를 돌려줍니다. 진입해도 되면 None."""
    lim = cfg["limits"]
    d = day_stats(state)
    if time.time() < state.get("pause_until", 0):
        until = datetime.fromtimestamp(state["pause_until"], KST).strftime("%m/%d %H:%M")
        return f"연속 손절 {lim['pause_after_losses']}번으로 {until}까지 쉬는 중"
    if d["pnl"] <= -lim["daily_loss_usdt"]:
        return f"오늘 손실 {d['pnl']:.2f} USDT로 하루 손실 한도(-{lim['daily_loss_usdt']} USDT) 도달, 내일 오전 9시까지 쉼"
    if d["entries"] >= lim["max_entries_per_day"]:
        return f"오늘 진입 {d['entries']}번으로 하루 진입 한도({lim['max_entries_per_day']}번) 도달"
    held = open_positions(state)
    if len(held) >= lim["max_open_positions"]:
        names = ", ".join(sym.replace("USDT", "") for sym, _ in held)
        return f"이미 포지션 {len(held)}개 보유 중 ({names}, 모든 코인 합쳐 동시 {lim['max_open_positions']}개까지)"
    return None


def limit_line(cfg, state):
    d = day_stats(state)
    lim = cfg["limits"]
    return (f"오늘 한도: 진입 {d['entries']}/{lim['max_entries_per_day']}번 · "
            f"손익 {d['pnl']:+.2f} USDT (한도 -{lim['daily_loss_usdt']}) · 연속 손절 {state.get('loss_streak', 0)}번")


def blocked_header(reason):
    return [f"📌 참고용 · 진입하지 마세요: {reason}", "(조건은 맞았지만 하루 한도 때문에 포지션으로 기록하지 않습니다.)", ""]


def record_pnl(cfg, state, tg, pnl, closed):
    """손익을 오늘·누적 성적에 더하고, 한도에 걸리면 알립니다."""
    lim = cfg["limits"]
    d = day_stats(state)
    d["pnl"] += pnl
    state["total_pnl"] = state.get("total_pnl", 0.0) + pnl
    if not closed:
        return
    state["trades"] = state.get("trades", 0) + 1
    if state.get("pos_pnl", 0.0) + pnl > 0:
        state["wins"] = state.get("wins", 0) + 1
        state["loss_streak"] = 0
    else:
        state["loss_streak"] = state.get("loss_streak", 0) + 1
    state["pos_pnl"] = 0.0
    if state["loss_streak"] >= lim["pause_after_losses"]:
        state["pause_until"] = time.time() + lim["pause_hours"] * HOUR
        state["loss_streak"] = 0
        until = datetime.fromtimestamp(state["pause_until"], KST).strftime("%m/%d %H:%M")
        tg.send(f"⏸ {lim['pause_after_losses']}번 연속 손절이라 {until}까지 새 진입 알림을 쉽니다. 감정 매매를 막기 위한 규칙이에요.")
    if d["pnl"] <= -lim["daily_loss_usdt"] and not d["loss_notice"]:
        d["loss_notice"] = True
        tg.send(f"⏸ 오늘 손실이 {d['pnl']:.2f} USDT로 하루 한도에 닿았습니다. 내일 오전 9시까지 새 진입 알림은 참고용으로만 보냅니다.")


def add_partial(state, pnl):
    state["pos_pnl"] = state.get("pos_pnl", 0.0) + pnl


# ---------------------------------------------------------------- 자동 주문 (기본 꺼짐)

class Trader:
    """config.json 의 trade_mode 가 off 이면 아무 주문도 내지 않습니다.
    demo 는 비트겟 모의투자, live 는 실제 계좌입니다. 키는 GitHub 비밀값에서만 읽습니다."""

    def __init__(self, cfg):
        self.cfg = cfg
        self.mode = cfg.get("trade_mode", "off")
        self.key = os.environ.get("BITGET_API_KEY", "").strip()
        self.secret = os.environ.get("BITGET_API_SECRET", "").strip()
        self.passphrase = os.environ.get("BITGET_PASSPHRASE", "").strip()
        self.ready = set()
        self.specs = {}
        self.note = None
        if self.mode not in ("off", "demo", "live"):
            self.note = f"trade_mode 값 '{self.mode}'를 알 수 없어 주문을 끕니다."
            self.mode = "off"
        if self.mode != "off" and not (self.key and self.secret and self.passphrase):
            self.note = "비트겟 API 키 비밀값이 없어 자동 주문을 끕니다."
            self.mode = "off"
        self.label = {"demo": "모의투자", "live": "실전"}.get(self.mode)

    @property
    def on(self):
        return self.mode != "off"

    def request(self, method, path, params=None, body=None):
        query = ("?" + urllib.parse.urlencode(params)) if params else ""
        data = json.dumps(body) if body is not None else ""
        ts = str(int(time.time() * 1000))
        sign = base64.b64encode(hmac.new(self.secret.encode(), (ts + method + path + query + data).encode(),
                                         hashlib.sha256).digest()).decode()
        headers = {"ACCESS-KEY": self.key, "ACCESS-SIGN": sign, "ACCESS-TIMESTAMP": ts,
                   "ACCESS-PASSPHRASE": self.passphrase, "Content-Type": "application/json", "locale": "ko-KR"}
        if self.mode == "demo":
            headers["paptrading"] = "1"
        req = urllib.request.Request(API + path + query, data=data.encode() if data else None,
                                     headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=20) as r:
                res = json.load(r)
        except urllib.error.HTTPError as e:
            res = json.loads(e.read() or b"{}")
        if res.get("code") != "00000":
            raise RuntimeError(f"{res.get('code')} {res.get('msg')}")
        return res.get("data")

    def base(self):
        return dict(symbol=SYMBOL, productType=PRODUCT, marginCoin="USDT")

    def spec(self):
        """코인별 가격 소수점, 수량 소수점, 최소 수량."""
        if SYMBOL not in self.specs:
            c = get_json("/api/v2/mix/market/contracts", dict(symbol=SYMBOL, productType=PRODUCT))[0]
            self.specs[SYMBOL] = dict(price=int(c["pricePlace"]), volume=int(c["volumePlace"]),
                                      min=float(c["minTradeNum"]))
        return self.specs[SYMBOL]

    def setup(self):
        if SYMBOL in self.ready:
            return
        try:
            self.request("POST", "/api/v2/mix/account/set-position-mode",
                         body=dict(productType=PRODUCT, posMode="one_way_mode"))
        except Exception:
            pass  # 이미 단방향이거나 포지션이 있으면 바꿀 수 없음 (그대로 진행)
        self.request("POST", "/api/v2/mix/account/set-margin-mode", body=dict(self.base(), marginMode="isolated"))
        self.request("POST", "/api/v2/mix/account/set-leverage",
                     body=dict(self.base(), leverage=str(self.cfg["leverage"])))
        self.ready.add(SYMBOL)

    def position(self):
        rows = self.request("GET", "/api/v2/mix/position/single-position", params=self.base()) or []
        return next((r for r in rows if float(r.get("total", 0)) > 0), None)

    def _size(self, usdt, price):
        q = 10 ** self.spec()["volume"]
        return math.floor(usdt / price * q) / q

    def _px(self, x):
        return f"{x:.{self.spec()['price']}f}"

    def _try(self, what, fn):
        if not self.on:
            return None
        try:
            self.setup()
            detail = fn()
            return f"🤖 {self.label} 주문 완료: {what}" + (f" ({detail})" if detail else "")
        except Exception as e:
            return f"⚠ {self.label} 주문 실패: {what} → {e}\n거래소 앱에서 직접 확인해 주세요."

    def open(self, side, usdt, price, stop, tp=None, add=False):
        def go():
            pos = self.position()
            if pos and not add:
                raise RuntimeError("거래소에 이미 포지션이 있어 새로 진입하지 않았습니다")
            size = self._size(usdt, price)
            if size < self.spec()["min"]:
                raise RuntimeError(f"주문 수량 {size} {COIN}가 최소 수량({self.spec()['min']})보다 작습니다")
            body = dict(self.base(), marginMode="isolated", size=str(size), side="buy" if side == 1 else "sell",
                        orderType="market", clientOid=f"alert{int(time.time() * 1000)}")
            if not add:
                body["presetStopLossPrice"] = self._px(stop)
                if tp:
                    body["presetStopSurplusPrice"] = self._px(tp)
            self.request("POST", "/api/v2/mix/order/place-order", body=body)
            if add:
                self._set_stop(side, stop)
            return f"{size} {COIN}, 손절 {self._px(stop)}" + (f", 익절 {self._px(tp)}" if tp and not add else "")
        return self._try(f"{COIN} {side_word(side)} {'추가' if add else '진입'} {usdt:.2f} USDT", go)

    def _set_stop(self, side, stop, tp=None):
        body = dict(self.base(), holdSide="buy" if side == 1 else "sell",
                    stopLossTriggerPrice=self._px(stop), stopLossTriggerType="mark_price")
        if tp:
            body.update(stopSurplusTriggerPrice=self._px(tp), stopSurplusTriggerType="mark_price")
        self.request("POST", "/api/v2/mix/order/place-pos-tpsl", body=body)

    def set_stop(self, side, stop, tp=None):
        return self._try(f"손절가 {fmt(stop)}로 변경", lambda: self._set_stop(side, stop, tp))

    def close(self, side, fraction=1.0):
        def go():
            pos = self.position()
            if not pos:
                return "거래소에서 이미 정리됨"
            q = 10 ** self.spec()["volume"]
            size = math.floor(float(pos["total"]) * fraction * q) / q
            if fraction < 1 and size < self.spec()["min"]:
                return "절반 수량이 최소 수량보다 작아 그대로 둠"
            if fraction >= 1:
                size = float(pos["total"])
            self.request("POST", "/api/v2/mix/order/place-order", body=dict(
                self.base(), marginMode="isolated", size=str(size), side="sell" if side == 1 else "buy",
                orderType="market", reduceOnly="YES", clientOid=f"close{int(time.time() * 1000)}"))
            return f"{size} {COIN}"
        return self._try(f"{COIN} {side_word(side)} {'절반 ' if fraction < 1 else ''}청산", go)


def send_with_order(tg, text, order_note):
    tg.send(text + (f"\n\n{order_note}" if order_note else ""))


# ---------------------------------------------------------------- 전략 C1 (일봉 터틀 20/10 + MACD)

def run_c1(cfg, state, tg, days, h1, info, trader):
    now = time.time()
    highs, lows, closes = [d[2] for d in days], [d[3] for d in days], [d[4] for d in days]
    direction, e50, e200 = trend_dir(closes)
    hist = macd_hist(closes)
    n_atr = atr(days, 20)[-1]
    hi20, lo20 = max(highs[-20:]), min(lows[-20:])
    hi10, lo10 = max(highs[-10:]), min(lows[-10:])
    today_start = days[-1][0] + 86400
    today = [c for c in h1 if c[0] >= today_start]
    price = info["price"]
    t_high = max([c[2] for c in today] + [price])
    t_low = min([c[3] for c in today] + [price])
    pos = state.get("c1_pos")
    day_key = datetime.fromtimestamp(today_start, timezone.utc).strftime("%Y-%m-%d")

    if pos:
        side = pos["side"]
        # 피라미딩: 마지막 단위에서 0.5N 유리하게 움직일 때마다 1단위 추가 (c1_max_units 까지, 기본 1 = 추가 없음)
        while len(pos["units"]) < pos.get("max_units", 1):
            nxt = pos["units"][-1] + side * 0.5 * pos["N"]
            if (price >= nxt) if side == 1 else (price <= nxt):
                pos["units"].append(nxt)
                pos["stop"] = nxt - side * 2 * pos["N"]
                send_with_order(tg, "\n".join([
                    f"[전략 C1 · {side_word(side)} 추가] {SYMBOL}",
                    f"{len(pos['units'])}번째 단위 추가 가격: {fmt(nxt)} (현재 {fmt(price)})",
                    f"추가 크기: {fmt(pos['unit_usdt'])} USDT",
                    f"전체 손절가를 {fmt(pos['stop'])}로 올리세요." if side == 1 else f"전체 손절가를 {fmt(pos['stop'])}로 내리세요.",
                ]), trader.open(side, pos["unit_usdt"], price, pos["stop"], add=True))
                journal("C1", "추가", side, nxt, pos["stop"])
            else:
                break
        exit_level = max(pos["stop"], lo10) if side == 1 else min(pos["stop"], hi10)
        hit = (t_low <= exit_level) if side == 1 else (t_high >= exit_level)
        if hit and now - pos["opened"] > HOUR:
            pnl = sum(pos["unit_usdt"] * ((exit_level / u - 1) * side - FEE_ROUND_TRIP) for u in pos["units"])
            reason = "손절가" if exit_level == pos["stop"] else ("10일 최저가 이탈" if side == 1 else "10일 최고가 돌파")
            state["c1_pos"] = None
            record_pnl(cfg, state, tg, pnl, closed=True)
            send_with_order(tg, "\n".join([
                f"[전략 C1 · {side_word(side)} 청산] {SYMBOL}",
                f"청산 기준: {reason} {fmt(exit_level)} (현재 {fmt(price)})",
                f"보유 단위 {len(pos['units'])}개, 수수료 포함 예상 손익 {pnl:+.2f} USDT",
                limit_line(cfg, state),
            ]), trader.close(side))
            journal("C1", "청산", side, exit_level, pnl=pnl, note=reason)
        return

    if not (cfg["strategies"].get("C1_turtle_macd") and cfg["coin"].get("C1")):
        return
    side = 0
    if direction == 1 and t_high > hi20 and price >= hi20 and hist[-1] > 0:
        side = 1
    elif direction == -1 and t_low < lo20 and price <= lo20 and hist[-1] < 0:
        side = -1
    if not side or state.get("c1_last_signal_day") == day_key:
        return
    state["c1_last_signal_day"] = day_key
    entry = price
    stop = entry - side * 2 * n_atr
    notional, dist, _ = sizing(cfg, entry, stop)
    if dist * 100 > cfg["stop_skip_pct"]:
        journal("C1", "건너뜀", side, entry, stop, note=f"손절 거리 {dist * 100:.1f}%")
        return
    max_units = cfg.get("c1_max_units", 1)
    unit = notional / max_units
    blocked = entry_block(cfg, state)
    order = None
    if not blocked:
        state["c1_pos"] = dict(side=side, units=[entry], N=n_atr, stop=stop, unit_usdt=unit, opened=now,
                              max_units=max_units)
        day_stats(state)["entries"] += 1
        order = trader.open(side, unit, entry, stop)
    level = hi20 if side == 1 else lo20
    send_with_order(tg, "\n".join([
        *(blocked_header(blocked) if blocked else []),
        f"[전략 C1 · {side_word(side)}] {SYMBOL} 20일 {'최고가 돌파' if side == 1 else '최저가 이탈'}",
        f"돌파 기준: {fmt(level)} / 현재가: {fmt(entry)}",
        "",
        "[진입 근거]",
        f"✔ 일봉 종가 {fmt(closes[-1])} {'>' if side == 1 else '<'} EMA200 {fmt(e200[-1])}, "
        f"EMA50 {fmt(e50[-1])} {'>' if side == 1 else '<'} EMA200 → {dir_word(direction)}",
        f"✔ 전날 일봉 MACD 히스토그램 {sfmt(hist[-1])} ({'양수' if side == 1 else '음수'}, 추세 힘 확인)",
        f"✔ 오늘 {'고가' if side == 1 else '저가'} {fmt(t_high if side == 1 else t_low)}가 20일 "
        f"{'최고가' if side == 1 else '최저가'} {fmt(level)}를 넘었고 현재가도 그 {'위' if side == 1 else '아래'}",
        f"✔ 손절 거리 {dist * 100:.1f}% (8% 이하라 알림 대상)",
        f"• 손절 근거: 20일 평균 변동폭 N={fmt(n_atr)}의 2배 (2N)",
        f"• 펀딩비 {info['funding'] * 100:.4f}% · {oi_trend_tag(state, side, [x[4] for x in h1])}",
        *liq_lines(info.get("liq"), entry, short=True),
        "",
        "[주문 계획]",
        (f"1단위 진입: {fmt(unit)} USDT (최대 {max_units}단위, 0.5N={fmt(0.5 * n_atr)}마다 추가 알림)" if max_units > 1
         else f"진입: {fmt(unit)} USDT 한 번에 (백테스트와 같은 방식, 추가 진입 없음)"),
        f"손절가: {fmt(stop)} ({-side * dist * 100:+.1f}%, 2N)",
        f"청산: 일봉이 10일 {'최저가' if side == 1 else '최고가'}({fmt(lo10 if side == 1 else hi10)})를 넘어가면 알림",
        *position_lines(cfg, entry, stop),
        time_tag(now),
        limit_line(cfg, state),
    ]), order)
    journal("C1", "참고용" if blocked else "진입", side, entry, stop, note=blocked or f"N={fmt(n_atr)}")


# ---------------------------------------------------------------- 전략 A (1시간봉 눌림목)

def a_checks(i, h1, ind, side, funding):
    """전략 A 조건을 하나씩 점검해 (충족 여부, 설명) 목록으로 돌려줍니다."""
    l, h = [x[3] for x in h1], [x[2] for x in h1]
    e20, e50, r, hist, vols = ind["e20"], ind["e50"], ind["rsi"], ind["hist"], [x[5] for x in h1]
    if side == 1:
        gap = min(min(abs(l[k] - e20[k]) / e20[k], abs(l[k] - e50[k]) / e50[k]) for k in range(i - 2, i + 1))
        rs = 40 <= min(r[i - 4:i + 1]) <= 50 and r[i] > r[i - 1]
        rs_txt = f"RSI가 40~50까지 내려왔다가(최저 {min(r[i - 4:i + 1]):.0f}) 다시 오름 ({r[i - 1]:.0f}→{r[i]:.0f})"
        mc = any(hist[k - 1] < 0 < hist[k] for k in range(i - 2, i + 1))
        mc_txt = "MACD 히스토그램이 음수에서 양수로 바뀜 (최근 3봉 안)"
        fu = funding < 0.0003
        fu_txt = f"펀딩비 {funding * 100:.4f}% < 0.03% (롱 과열 아님)"
        hot = r[i] < 75 and ind["mfi"][i] < 80 and ind["J"][i] < 100
        hot_txt = f"과열 아님: RSI {r[i]:.0f}<75, MFI {ind['mfi'][i]:.0f}<80, KDJ J {ind['J'][i]:.0f}<100"
    else:
        gap = min(min(abs(h[k] - e20[k]) / e20[k], abs(h[k] - e50[k]) / e50[k]) for k in range(i - 2, i + 1))
        rs = 50 <= max(r[i - 4:i + 1]) <= 60 and r[i] < r[i - 1]
        rs_txt = f"RSI가 50~60까지 올라왔다가(최고 {max(r[i - 4:i + 1]):.0f}) 다시 내림 ({r[i - 1]:.0f}→{r[i]:.0f})"
        mc = any(hist[k - 1] > 0 > hist[k] for k in range(i - 2, i + 1))
        mc_txt = "MACD 히스토그램이 양수에서 음수로 바뀜 (최근 3봉 안)"
        fu = funding > -0.0003
        fu_txt = f"펀딩비 {funding * 100:.4f}% > -0.03% (숏 과열 아님)"
        hot = r[i] > 25 and ind["mfi"][i] > 20 and ind["J"][i] > 0
        hot_txt = f"침체 아님: RSI {r[i]:.0f}>25, MFI {ind['mfi'][i]:.0f}>20, KDJ J {ind['J'][i]:.0f}>0"
    avg = sum(vols[i - 20:i]) / 20
    return [
        (gap <= 0.003, f"{'저가' if side == 1 else '고가'}가 EMA20({fmt(e20[i])})/EMA50({fmt(e50[i])})에 닿음 (거리 {gap * 100:.2f}% ≤ 0.3%)"),
        (rs, rs_txt),
        (mc, mc_txt),
        (vols[i] >= 1.5 * avg, f"거래량 {vols[i] / avg:.1f}배 (20봉 평균의 1.5배 이상)"),
        (fu, fu_txt),
        (hot, hot_txt),
    ]


def a_signal(i, h1, ind, trend4h, funding):
    if trend4h and all(ok for ok, _ in a_checks(i, h1, ind, trend4h, funding)):
        return trend4h
    return 0


def run_a(cfg, state, tg, h1, h4, daily_direction, info, trader):
    closes = [x[4] for x in h1]
    ks, ds, js = kdj(h1)
    ind = dict(e20=ema(closes, 20), e50=ema(closes, 50), rsi=rsi(closes), hist=macd_hist(closes),
               mfi=mfi(h1), J=js, atr=atr(h1, 14))
    t4_dir, _, _ = trend_dir([x[4] for x in h4])
    trend = t4_dir if t4_dir == daily_direction else 0
    last_done = state.get("a_last_bar", h1[-2][0])
    pos = state.get("a_pos")
    for i in range(len(h1) - 48, len(h1)):
        bar = h1[i]
        if bar[0] <= last_done:
            continue
        o, hi, lo, c = bar[1:5]
        if pos:
            side, stop = pos["side"], pos["stop"]
            done = None
            if (lo <= stop) if side == 1 else (hi >= stop):
                done = ("본전 청산" if pos["be"] else "손절", stop)
            elif not pos["be"] and ((hi >= pos["tp1"]) if side == 1 else (lo <= pos["tp1"])):
                pos["be"] = True
                pos["stop"] = pos["entry"]
                half = pos.get("usdt", 0) / 2 * ((pos["tp1"] / pos["entry"] - 1) * side - FEE_ROUND_TRIP)
                add_partial(state, half)
                record_pnl(cfg, state, tg, half, closed=False)
                note = trader.close(side, 0.5)
                if trader.on:
                    note += "\n" + trader.set_stop(side, pos["entry"], pos["tp2"])
                send_with_order(tg, f"[전략 A · {side_word(side)} 1차 익절] {SYMBOL} {fmt(pos['tp1'])} 도달\n"
                                    f"절반 청산하고 손절을 본전 {fmt(pos['entry'])}로 옮기세요.\n"
                                    f"절반 손익(수수료 포함) {half:+.2f} USDT", note)
                journal("A", "1차 익절", side, pos["tp1"], pnl=half)
            if not done and pos["be"] and ((hi >= pos["tp2"]) if side == 1 else (lo <= pos["tp2"])):
                done = ("2차 익절", pos["tp2"])
            if not done and ((c < ind["e20"][i]) if side == 1 else (c > ind["e20"][i])) and bar[0] > pos["opened_bar"]:
                done = ("1시간봉 EMA20 이탈 청산", c)
            if done:
                rest = 0.5 if pos["be"] else 1.0
                pnl = pos.get("usdt", 0) * rest * ((done[1] / pos["entry"] - 1) * side - FEE_ROUND_TRIP)
                pos = None
                state["a_pos"] = None
                record_pnl(cfg, state, tg, pnl, closed=True)
                send_with_order(tg, f"[전략 A · {side_word(side)} 종료] {SYMBOL} {done[0]} {fmt(done[1])}\n남은 물량을 정리하세요.\n"
                                    f"남은 물량 손익(수수료 포함) {pnl:+.2f} USDT\n{limit_line(cfg, state)}",
                                trader.close(side))
                journal("A", done[0], side, done[1], pnl=pnl)
        elif cfg["strategies"].get("A_pullback") and cfg["coin"].get("A") and i == len(h1) - 1:
            side = a_signal(i, h1, ind, trend, info["funding"])
            if side:
                entry = info["price"]
                sd = 1.5 * ind["atr"][i]
                stop = entry - side * sd
                _, dist, _ = sizing(cfg, entry, stop)
                if dist * 100 > cfg["stop_skip_pct"]:
                    journal("A", "건너뜀", side, entry, stop)
                else:
                    tp1, tp2 = entry + side * 2 * sd, entry + side * 3 * sd
                    notional = sizing(cfg, entry, stop)[0]
                    state["a_pos"] = pos
                    blocked = entry_block(cfg, state)
                    order = None
                    if not blocked:
                        pos = dict(side=side, entry=entry, stop=stop, tp1=tp1, tp2=tp2, be=False,
                                   opened_bar=bar[0], usdt=notional)
                        day_stats(state)["entries"] += 1
                        order = trader.open(side, notional, entry, stop, tp2)
                    oi_tag = oi_trend_tag(state, side, closes)
                    send_with_order(tg, "\n".join([
                        *(blocked_header(blocked) if blocked else []),
                        f"[전략 A · {side_word(side)}] {SYMBOL} 1시간봉 추세 눌림목",
                        f"진입가: {fmt(entry)}",
                        "",
                        "[진입 근거]",
                        f"✔ 일봉 방향 {dir_word(daily_direction)}, 4시간봉도 같은 방향 (종가·EMA50이 EMA200 {'위' if side == 1 else '아래'})",
                        *[f"✔ {t}" for _, t in a_checks(i, h1, ind, side, info["funding"])],
                        f"• 손절 근거: 1시간봉 평균 변동폭(ATR14) {fmt(ind['atr'][i])}의 1.5배",
                        *liq_lines(info.get("liq"), entry, short=True),
                        "",
                        "[주문 계획]",
                        f"손절가: {fmt(stop)} ({-side * dist * 100:+.1f}%)",
                        f"1차 익절: {fmt(tp1)} (절반 청산 후 손절을 본전으로)",
                        f"2차 익절: {fmt(tp2)} 또는 1시간봉이 EMA20 반대편 마감 시",
                        *position_lines(cfg, entry, stop),
                        f"펀딩비 {info['funding'] * 100:.4f}% · {oi_tag} · {time_tag(time.time())}",
                        indicator_line(h1, ind, i, ks, ds),
                        limit_line(cfg, state),
                    ]), order)
                    journal("A", "참고용" if blocked else "진입", side, entry, stop, tp1, tp2, note=blocked or "")
        last_done = bar[0]
    state["a_last_bar"] = last_done
    state["a_pos"] = pos


def indicator_line(cs, ind, i, ks, ds):
    lo, mid, up = bollinger([x[4] for x in cs], i)
    return (f"참고 지표: RSI {ind['rsi'][i]:.0f} · MFI {ind['mfi'][i]:.0f} · "
            f"KDJ K{ks[i]:.0f}/D{ds[i]:.0f}/J{ind['J'][i]:.0f} · MACD {'+' if ind['hist'][i] > 0 else '−'} · "
            f"볼린저 {fmt(lo)}~{fmt(up)}")


def oi_trend_tag(state, side, closes):
    hist = state.get("oi_history", [])
    past = [x for x in hist if x[0] <= time.time() - 4 * HOUR]
    if not past or not hist:
        return "OI 기록 쌓는 중"
    rising = hist[-1][1] > past[-1][1]
    price_up = closes[-1] > closes[-5]
    if rising and price_up == (side == 1):
        return "OI 증가 ✔"
    return "OI 증가 아님"


# ---------------------------------------------------------------- 매일 요약

def daily_summary(cfg, state, tg, days, h4, info, force=False, show_ops=True):
    day_key = datetime.fromtimestamp(days[-1][0], timezone.utc).strftime("%Y-%m-%d")
    if state.get("summary_day") == day_key and not force:
        return
    state["summary_day"] = day_key
    closes = [d[4] for d in days]
    c = closes[-1]
    price = info["price"]
    direction, e50, e200 = trend_dir(closes)
    hist = macd_hist(closes)
    h4c = [x[4] for x in h4]
    d4, e4_50, e4_200 = trend_dir(h4c)
    n = atr(days, 14)[-1]
    n20 = atr(days, 20)[-1]
    r = rsi(closes)[-1]
    m = mfi(days)[-1]
    _, _, js = kdj(days)
    bl, bm, bu = bollinger(closes, len(closes) - 1)
    hi20, lo20 = max(d[2] for d in days[-20:]), min(d[3] for d in days[-20:])
    ok = lambda b: "✔" if b else "✘"
    pct = lambda a, b: (a / b - 1) * 100

    lines = [
        f"[오늘의 시장 방향 · {COIN}] {datetime.now(KST).strftime('%m월 %d일')} (한국 시간 오전 9시 마감 일봉 기준)",
        f"판단: {dir_word(direction)}",
        "",
        "[판단 근거 · 일봉]",
        f"{ok(c > e200[-1])} 종가 {fmt(c)} {'>' if c > e200[-1] else '<'} EMA200 {fmt(e200[-1])} ({pct(c, e200[-1]):+.1f}%)",
        f"{ok(e50[-1] > e200[-1])} EMA50 {fmt(e50[-1])} {'>' if e50[-1] > e200[-1] else '<'} EMA200 "
        + ("(정배열, 상승 추세)" if e50[-1] > e200[-1] else "(역배열, 하락 추세)"),
        "→ 두 조건이 모두 위쪽이면 '롱만', 모두 아래쪽이면 '숏만', 엇갈리면 '쉬어감'입니다.",
        f"4시간봉: {dir_word(d4)} (종가 {fmt(h4c[-1])} · EMA50 {fmt(e4_50[-1])} · EMA200 {fmt(e4_200[-1])})"
        + (" → 이 코인은 전략 A를 쓰지 않습니다 (백테스트에서 손해)." if not cfg["coin"].get("A")
           else " → 일봉과 같은 방향이라 전략 A 신호를 받습니다." if d4 == direction and d4
           else " → 일봉과 방향이 달라 전략 A는 쉬어갑니다."),
        "",
        "[보조 지표 · 일봉]",
        f"• MACD 히스토그램 {sfmt(hist[-1])} ({'전날보다 커짐' if hist[-1] > hist[-2] else '전날보다 작아짐'}): "
        + ("상승 힘이 우세" if hist[-1] > 0 else "하락 힘이 우세"),
        f"• RSI14 {r:.0f}: " + ("과매수(70 이상)" if r >= 70 else "과매도(30 이하)" if r <= 30 else "중립 구간(30~70)"),
        f"• MFI14 {m:.0f}: " + ("자금 유입 과열(80 이상)" if m >= 80 else "자금 유출 과다(20 이하)" if m <= 20 else "중립 구간(20~80)"),
        f"• KDJ J {js[-1]:.0f}: " + ("단기 과열(100 이상)" if js[-1] >= 100 else "단기 침체(0 이하)" if js[-1] <= 0 else "보통"),
        f"• 볼린저밴드 {fmt(bl)}~{fmt(bu)} (중앙 {fmt(bm)}), 밴드 안 위치 {(c - bl) / (bu - bl) * 100:.0f}%",
        f"• 하루 평균 변동폭(ATR14) {fmt(n)} ({n / c * 100:.1f}%)",
        "",
        "[전략 C1 점검 · 20일 터틀]",
    ]
    if not cfg["coin"].get("C1"):
        lines.append("이 코인은 전략 C1을 쓰지 않습니다 (손절 거리가 대부분 8%를 넘어 10배로는 위험).")
    elif direction:
        level = hi20 if direction == 1 else lo20
        macd_ok = (hist[-1] > 0) == (direction == 1)
        stop_pct = 2 * n20 / c * 100
        lines += [
            f"{ok(True)} 방향: {dir_word(direction)}",
            f"{ok(macd_ok)} 일봉 MACD {'양수' if hist[-1] > 0 else '음수'}"
            + ("" if macd_ok else " → 돌파가 나와도 알림을 보내지 않습니다"),
            f"… 20일 {'최고가' if direction == 1 else '최저가'} {fmt(level)}까지 {pct(level, price):+.1f}% 남음 (돌파 시 알림)",
            f"   예상 손절 거리 2N = {stop_pct:.1f}%"
            + (" (8% 초과라 알림 안 함)" if stop_pct > 8 else " (5% 초과, 경고 대상)" if stop_pct > 5 else ""),
        ]
    else:
        lines.append(f"✘ 방향이 엇갈려 신호를 받지 않습니다. (20일 최고 {fmt(hi20)} / 최저 {fmt(lo20)})")

    f = info["funding"] * 100
    lines += [
        "",
        "[수급 · 심리]",
        f"• 펀딩비 {f:.4f}%: " + ("롱 과열(0.03% 이상), 롱 진입 조심" if f >= 0.03 else
                                 "숏 과열(-0.03% 이하), 숏 진입 조심" if f <= -0.03 else "중립"),
        f"• 미결제약정 {info['oi']:,.0f} {COIN} (약 {info['oi'] * price / 1e8:,.1f}억 달러)" + oi_change_text(state),
    ]
    if info["ls_ratio"]:
        acc_long = info["ls_ratio"] / (1 + info["ls_ratio"]) * 100
        lines.append(f"• 계정 수 기준 롱 {acc_long:.0f}% / 숏 {100 - acc_long:.0f}% (사람 수 기준)")
    if info["long_share"]:
        lines.append(f"• 포지션 규모 기준 롱 {info['long_share'] * 100:.0f}% / 숏 {100 - info['long_share'] * 100:.0f}% (금액 기준)")
    lines += [""] + liq_lines(info.get("liq"), price)
    if (e50[-1] > e200[-1]) != (e50[-2] > e200[-2]):
        lines.append("★ 골든크로스 발생 (EMA50이 EMA200 위로)" if e50[-1] > e200[-1] else "★ 데드크로스 발생 (EMA50이 EMA200 아래로)")
    if not cfg.get("liquidity_switch_on", True):
        lines.append("유동성 스위치 꺼짐: 롱 신호는 역풍 구간입니다.")
    if not show_ops:
        tg.send("\n".join(lines))
        return
    lines += ["", "[운영 현황 · 모든 코인 합산]"]
    run = cfg.get("paper_run")
    if run:
        start = datetime.strptime(run["start"], "%Y-%m-%d").date()
        end = datetime.strptime(run["end"], "%Y-%m-%d").date()
        n_day = (datetime.strptime(day_key_kst(), "%Y-%m-%d").date() - start).days + 1
        tag = f"{n_day}일차" if n_day <= (end - start).days + 1 else "종료, 결과를 함께 점검할 때예요"
        lines.append(f"• 모의 운영 {start:%m/%d}~{end:%m/%d}: {tag}")
    trades, wins = state.get("trades", 0), state.get("wins", 0)
    lines.append(f"• 누적 성적: 거래 {trades}번, 이익 {wins}번, 손익 {state.get('total_pnl', 0.0):+.2f} USDT (수수료 포함 추정)")
    lines.append("• " + limit_line(cfg, state))
    lines.append(f"• 자동 주문: {dict(off='꺼짐 (알림만)', demo='모의투자', live='실전').get(cfg.get('trade_mode', 'off'), '꺼짐')}")
    for sym, key in open_positions(state):
        pos = state.root["coins"][sym][key]
        lines.append(f"• 보유 중({sym.replace('USDT', '')} {key[:-4].upper()}): {side_word(pos['side'])}, 손절가 {fmt(pos['stop'])}")
    tg.send("\n".join(lines))


def oi_change_text(state):
    hist = state.get("oi_history", [])
    past = [x for x in hist if x[0] <= time.time() - 23 * HOUR]
    if not past:
        return " (24시간 변화는 기록이 쌓이면 표시)"
    chg = (hist[-1][1] / past[-1][1] - 1) * 100
    return f", 24시간 {chg:+.1f}% " + ("(새 포지션 유입)" if chg > 0 else "(포지션 정리)")


# ---------------------------------------------------------------- 실행

def main():
    global SYMBOL, COIN
    with open(CONFIG_PATH, encoding="utf-8") as f:
        cfg = json.load(f)
    root = load_state()
    tg = Telegram(root)
    if tg.token and not tg.ready():
        save_state(root)
        return
    cfg.setdefault("limits", dict(max_open_positions=1, max_entries_per_day=2, daily_loss_usdt=2,
                                  pause_after_losses=3, pause_hours=24))
    force = os.environ.get("FORCE_SUMMARY") == "1"
    trader = Trader(cfg)
    if trader.note and root.get("trader_note") != trader.note:
        tg.send("⚠ " + trader.note)
    root["trader_note"] = trader.note
    coins = cfg.get("coins", DEFAULT_COINS)
    failed = []
    for n, (symbol, coin_cfg) in enumerate(coins.items()):
        SYMBOL, COIN = symbol, symbol.replace("USDT", "")
        cfg["coin"] = coin_cfg
        try:
            run_coin(cfg, CoinState(root, symbol), tg, trader, force, show_ops=n == len(coins) - 1)
        except Exception as e:  # 한 코인이 실패해도 다른 코인은 계속 검사합니다.
            print(f"{symbol} 오류:", e)
            failed.append(symbol)
    root["last_run"] = datetime.now(KST).strftime("%Y-%m-%d %H:%M")
    save_state(root)
    print("완료:", root["last_run"])
    if failed:
        sys.exit(1)


def run_coin(cfg, state, tg, trader, force, show_ops):
    h1 = candles("1H", HOUR)
    h4 = candles("4H", 4 * HOUR)
    days = daily_candles()
    info = market_info()
    info["liq"] = liquidation_map(h1, info["price"], info["long_share"])

    hist = state.get("oi_history", [])
    hist.append([int(time.time()), info["oi"]])
    state["oi_history"] = hist[-72:]

    direction, _, _ = trend_dir([d[4] for d in days])
    daily_summary(cfg, state, tg, days, h4, info, force=force, show_ops=show_ops)
    run_c1(cfg, state, tg, days, h1, info, trader)
    run_a(cfg, state, tg, h1, h4, direction, info, trader)
    print(SYMBOL, "가격", info["price"])


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print("오류:", e)
        sys.exit(1)
