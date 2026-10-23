"""비트겟 BTCUSDT 선물 알림 봇 (주문 없음, 텔레그램 알림만).
 
GitHub Actions가 매시간 실행합니다. 규칙은 'BTC 선물 알림 전략 규칙표' 문서를 따릅니다.
- 전략 C1: 20일 터틀 돌파 + 전날 일봉 MACD 확인 (주력)
- 전략 A: 4시간봉 추세 + 1시간봉 눌림목 + 과열 회피
- 매일 한국 시간 오전 9시 시장 방향 요약
"""
import csv
import json
import os
import sys
import time
import urllib.parse
import urllib.request
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
 
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATE_PATH = os.path.join(ROOT, "state", "state.json")
JOURNAL_PATH = os.path.join(ROOT, "state", "journal.csv")
CONFIG_PATH = os.path.join(ROOT, "config.json")
 
API = "https://api.bitget.com"
SYMBOL = "BTCUSDT"
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
    return dict(
        price=float(t["lastPr"]),
        funding=float(t["fundingRate"]),
        oi=float(oi["openInterestList"][0]["size"]),
        ls_ratio=ls_ratio,
    )
 
 
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
    return f"{x:,.0f}" if abs(x) >= 100 else f"{x:,.2f}"
 
 
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
    if os.path.exists(STATE_PATH):
        with open(STATE_PATH, encoding="utf-8") as f:
            return json.load(f)
    return {}
 
 
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
        w.writerow([datetime.now(KST).strftime("%Y-%m-%d %H:%M"), strategy, event,
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
 
 
# ---------------------------------------------------------------- 전략 C1 (일봉 터틀 20/10 + MACD)
 
def run_c1(cfg, state, tg, days, h1, info):
    now = time.time()
    highs, lows, closes = [d[2] for d in days], [d[3] for d in days], [d[4] for d in days]
    direction, _, _ = trend_dir(closes)
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
        # 피라미딩: 마지막 단위에서 0.5N 유리하게 움직일 때마다 1단위 추가 (최대 4단위)
        while len(pos["units"]) < 4:
            nxt = pos["units"][-1] + side * 0.5 * pos["N"]
            if (price >= nxt) if side == 1 else (price <= nxt):
                pos["units"].append(nxt)
                pos["stop"] = nxt - side * 2 * pos["N"]
                tg.send("\n".join([
                    f"[전략 C1 · {side_word(side)} 추가] BTCUSDT",
                    f"{len(pos['units'])}번째 단위 추가 가격: {fmt(nxt)} (현재 {fmt(price)})",
                    f"추가 크기: {fmt(pos['unit_usdt'])} USDT",
                    f"전체 손절가를 {fmt(pos['stop'])}로 올리세요." if side == 1 else f"전체 손절가를 {fmt(pos['stop'])}로 내리세요.",
                ]))
                journal("C1", "추가", side, nxt, pos["stop"])
            else:
                break
        exit_level = max(pos["stop"], lo10) if side == 1 else min(pos["stop"], hi10)
        hit = (t_low <= exit_level) if side == 1 else (t_high >= exit_level)
        if hit and now - pos["opened"] > HOUR:
            pnl = sum(pos["unit_usdt"] * (exit_level / u - 1) * side for u in pos["units"])
            reason = "손절가" if exit_level == pos["stop"] else ("10일 최저가 이탈" if side == 1 else "10일 최고가 돌파")
            tg.send("\n".join([
                f"[전략 C1 · {side_word(side)} 청산] BTCUSDT",
                f"청산 기준: {reason} {fmt(exit_level)} (현재 {fmt(price)})",
                f"보유 단위 {len(pos['units'])}개, 수수료 전 예상 손익 {pnl:+.2f} USDT",
            ]))
            journal("C1", "청산", side, exit_level, pnl=pnl, note=reason)
            state["c1_pos"] = None
        return
 
    if not cfg["strategies"].get("C1_turtle_macd"):
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
    unit = notional / 4
    state["c1_pos"] = dict(side=side, units=[entry], N=n_atr, stop=stop, unit_usdt=unit, opened=now)
    level = hi20 if side == 1 else lo20
    tg.send("\n".join([
        f"[전략 C1 · {side_word(side)}] BTCUSDT 20일 {'최고가 돌파' if side == 1 else '최저가 이탈'}",
        f"시장 방향: {dir_word(direction)} · 전날 일봉 MACD 확인 ✔",
        f"돌파 기준: {fmt(level)} / 현재가: {fmt(entry)}",
        f"1단위 진입: {fmt(unit)} USDT (최대 4단위, 0.5N={fmt(0.5 * n_atr)}마다 추가 알림)",
        f"손절가: {fmt(stop)} ({-side * dist * 100:+.1f}%, 2N)",
        f"청산: 일봉이 10일 {'최저가' if side == 1 else '최고가'}({fmt(lo10 if side == 1 else hi10)})를 넘어가면 알림",
        *position_lines(cfg, entry, stop),
        time_tag(now),
    ]))
    journal("C1", "진입", side, entry, stop, note=f"N={n_atr:.0f}")
 
 
# ---------------------------------------------------------------- 전략 A (1시간봉 눌림목)
 
def a_signal(i, h1, ind, trend4h, funding):
    l, h = [x[3] for x in h1], [x[2] for x in h1]
    e20, e50, r, hist, vols = ind["e20"], ind["e50"], ind["rsi"], ind["hist"], [x[5] for x in h1]
    for side in (1, -1):
        if trend4h != side:
            continue
        if side == 1:
            pb = any(min(abs(l[k] - e20[k]) / e20[k], abs(l[k] - e50[k]) / e50[k]) <= 0.003 for k in range(i - 2, i + 1))
            rs = 40 <= min(r[i - 4:i + 1]) <= 50 and r[i] > r[i - 1]
            mc = any(hist[k - 1] < 0 < hist[k] for k in range(i - 2, i + 1))
            fu = funding < 0.0003
            hot = ind["rsi"][i] < 75 and ind["mfi"][i] < 80 and ind["J"][i] < 100
        else:
            pb = any(min(abs(h[k] - e20[k]) / e20[k], abs(h[k] - e50[k]) / e50[k]) <= 0.003 for k in range(i - 2, i + 1))
            rs = 50 <= max(r[i - 4:i + 1]) <= 60 and r[i] < r[i - 1]
            mc = any(hist[k - 1] > 0 > hist[k] for k in range(i - 2, i + 1))
            fu = funding > -0.0003
            hot = ind["rsi"][i] > 25 and ind["mfi"][i] > 20 and ind["J"][i] > 0
        vo = vols[i] >= 1.5 * sum(vols[i - 20:i]) / 20
        if pb and rs and mc and vo and fu and hot:
            return side
    return 0
 
 
def run_a(cfg, state, tg, h1, h4, daily_direction, info):
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
                tg.send(f"[전략 A · {side_word(side)} 1차 익절] {fmt(pos['tp1'])} 도달\n절반 청산하고 손절을 본전 {fmt(pos['entry'])}로 옮기세요.")
                journal("A", "1차 익절", side, pos["tp1"])
            if not done and pos["be"] and ((hi >= pos["tp2"]) if side == 1 else (lo <= pos["tp2"])):
                done = ("2차 익절", pos["tp2"])
            if not done and ((c < ind["e20"][i]) if side == 1 else (c > ind["e20"][i])) and bar[0] > pos["opened_bar"]:
                done = ("1시간봉 EMA20 이탈 청산", c)
            if done:
                tg.send(f"[전략 A · {side_word(side)} 종료] {done[0]} {fmt(done[1])}\n남은 물량을 정리하세요.")
                journal("A", done[0], side, done[1])
                pos = None
        elif cfg["strategies"].get("A_pullback") and i == len(h1) - 1:
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
                    pos = dict(side=side, entry=entry, stop=stop, tp1=tp1, tp2=tp2, be=False, opened_bar=bar[0])
                    oi_tag = oi_trend_tag(state, side, closes)
                    tg.send("\n".join([
                        f"[전략 A · {side_word(side)}] BTCUSDT 1시간봉 추세 눌림목",
                        f"시장 방향: {dir_word(daily_direction)} · 4시간봉 EMA200 {'위' if side == 1 else '아래'}",
                        f"진입가: {fmt(entry)}",
                        f"손절가: {fmt(stop)} ({-side * dist * 100:+.1f}%)",
                        f"1차 익절: {fmt(tp1)} (절반 청산 후 손절을 본전으로)",
                        f"2차 익절: {fmt(tp2)} 또는 1시간봉이 EMA20 반대편 마감 시",
                        *position_lines(cfg, entry, stop),
                        f"펀딩비 {info['funding'] * 100:.4f}% · {oi_tag} · {time_tag(time.time())}",
                        indicator_line(h1, ind, i, ks, ds),
                    ]))
                    journal("A", "진입", side, entry, stop, tp1, tp2)
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
 
def daily_summary(cfg, state, tg, days, h4, info, force=False):
    day_key = datetime.fromtimestamp(days[-1][0], timezone.utc).strftime("%Y-%m-%d")
    if state.get("summary_day") == day_key and not force:
        return
    state["summary_day"] = day_key
    closes = [d[4] for d in days]
    direction, e50, e200 = trend_dir(closes)
    hist = macd_hist(closes)
    d4, e4_50, e4_200 = trend_dir([x[4] for x in h4])
    n = atr(days, 14)[-1]
    lines = [
        f"[오늘의 시장 방향] {datetime.now(KST).strftime('%m월 %d일')}",
        f"판단: {dir_word(direction)}",
        f"일봉 종가 {fmt(closes[-1])} · EMA50 {fmt(e50[-1])} · EMA200 {fmt(e200[-1])}",
        f"4시간봉: {dir_word(d4)} (EMA50 {fmt(e4_50[-1])} / EMA200 {fmt(e4_200[-1])})",
        f"일봉 MACD 히스토그램 {'양수' if hist[-1] > 0 else '음수'} → 터틀 확인 조건 "
        + ("해당 없음" if not direction else ("충족" if (hist[-1] > 0) == (direction == 1) else "미충족 (돌파가 나와도 알림 안 함)")),
        f"20일 최고가 {fmt(max(d[2] for d in days[-20:]))} / 20일 최저가 {fmt(min(d[3] for d in days[-20:]))}",
        f"하루 평균 변동폭(ATR14) {fmt(n)} ({n / closes[-1] * 100:.1f}%)",
        f"펀딩비 {info['funding'] * 100:.4f}% · 미결제약정 {info['oi']:,.0f} BTC",
    ]
    if info["ls_ratio"]:
        lines.append(f"롱/숏 계정 비율 {info['ls_ratio']:.2f}")
    if (e50[-1] > e200[-1]) != (e50[-2] > e200[-2]):
        lines.append("★ 골든크로스 발생 (EMA50이 EMA200 위로)" if e50[-1] > e200[-1] else "★ 데드크로스 발생 (EMA50이 EMA200 아래로)")
    if not cfg.get("liquidity_switch_on", True):
        lines.append("유동성 스위치 꺼짐: 롱 신호는 역풍 구간입니다.")
    pos = state.get("c1_pos")
    if pos:
        lines.append(f"보유 중(C1): {side_word(pos['side'])} {len(pos['units'])}단위, 손절가 {fmt(pos['stop'])}")
    tg.send("\n".join(lines))
 
 
# ---------------------------------------------------------------- 실행
 
def main():
    with open(CONFIG_PATH, encoding="utf-8") as f:
        cfg = json.load(f)
    state = load_state()
    tg = Telegram(state)
    if tg.token and not tg.ready():
        save_state(state)
        return
    h1 = candles("1H", HOUR)
    h4 = candles("4H", 4 * HOUR)
    days = daily_candles()
    info = market_info()
 
    hist = state.get("oi_history", [])
    hist.append([int(time.time()), info["oi"]])
    state["oi_history"] = hist[-72:]
 
    direction, _, _ = trend_dir([d[4] for d in days])
    force = os.environ.get("FORCE_SUMMARY") == "1"
    daily_summary(cfg, state, tg, days, h4, info, force=force)
    run_c1(cfg, state, tg, days, h1, info)
    run_a(cfg, state, tg, h1, h4, direction, info)
    state["last_run"] = datetime.now(KST).strftime("%Y-%m-%d %H:%M")
    save_state(state)
    print("완료:", state["last_run"], "가격", info["price"])
 
 
if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print("오류:", e)
        sys.exit(1)
