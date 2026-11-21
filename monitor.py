#!/usr/bin/env python3
"""
visaMonitor -- US visa appointment availability monitor.

Watches the public H-1B availability calendar on https://qmq.app for the
five Mainland China consulates and sends a phone push (via ntfy.sh) when an
appointment date on/before the configured cutoff appears. Remembers what it already alerted so you are not notified twice
for the same date.

The source may render its appointment calendar client-side. This monitor
only trusts identifiable, city-specific H-1B listings in the rendered DOM;
a homepage containing only global booking successes is an explicit scrape
failure, not evidence of available appointments.

Config is via environment variables (see CONFIG below) with sensible defaults.
Run `python3 monitor.py --once` to check a single time (used by the scheduler).
"""

import argparse
import datetime as dt
import json
import os
import queue
import random
import re
import signal
import sys
import threading
import time
import urllib.parse
import urllib.request
from pathlib import Path
from zoneinfo import ZoneInfo

# --------------------------------------------------------------------------- #
# Config (override with env vars, all prefixed VISA_)
# --------------------------------------------------------------------------- #
def _env(name: str, default: str = "", legacy: str = "") -> str:
    """Read VISA_<name>, falling back to the legacy QMQ_<legacy or name>.

    An env var that is set but EMPTY counts as unset -- GitHub Actions renders an
    undefined `vars.X` as "", which would otherwise blow away the default (an
    empty VISA_TYPE, for instance, would match every visa type).
    """
    for key in (f"VISA_{name}", f"QMQ_{legacy or name}"):
        val = os.environ.get(key)
        if val not in (None, ""):
            return val
    return default


# This deployment is intentionally H-1B-only and Mainland-China-only.
# Ignore a stale/incorrect repo variable rather than silently watching F-1 or HK.
CITIES = ["广州", "北京", "上海", "沈阳", "武汉"]
VISA_PREFIX = "H-1B"
# Match every H-1B subcategory. Ignore legacy VISA_DESC / DESC_BY_CITY
# values that may have been configured for an older F-1 monitor.
DESC_CONTAINS = ""
DESC_BY_CITY: dict[str, str] = {}
# Alert on dates ON OR BEFORE this (inclusive, ISO yyyy-mm-dd).
# No meaningful default is possible, so fall back to "60 days out" -- set
# VISA_CUTOFF to your real target date.
CUTOFF = _env("CUTOFF") or (dt.date.today() + dt.timedelta(days=60)).isoformat()
# "官方紧急申请 - 不是普通号" rows are emergency-only slots (not bookable by regular
# applicants). Excluded by default; set VISA_INCLUDE_EMERGENCY=1 to include them.
INCLUDE_EMERGENCY = _env("INCLUDE_EMERGENCY").strip().lower() in ("1", "true", "yes", "on")
# Visa badges that share the SAME emergency (官方紧急申请) slot pool. At these
# consulates F-1 and J-1 draw on one pool, so the emergency view must look at
# both or it will under-report. Used only by the "emergency status" view.
EMERGENCY_TYPES = [t.strip() for t in _env("EMERGENCY_TYPES", "F-1,J-1").split(",") if t.strip()]
# When a NEW matching date appears, repeat the push this many times, this many
# seconds apart, so you don't overlook it.
PUSH_REPEAT = max(1, int(_env("PUSH_REPEAT", "6") or 6))
PUSH_INTERVAL = max(0, int(_env("PUSH_INTERVAL", "5") or 5))
# Slots are released on the hour and half hour, so a fixed 60s poll samples the
# critical seconds at random. Around each mark we poll much faster.
# NOTE: these are minutes-of-the-hour, which are identical in any whole-hour
# timezone -- :30 local is :30 Beijing -- so no timezone conversion is needed.
BURST_MARKS = [int(x) for x in _env("BURST_MINUTES", "0,30").split(",") if x.strip().isdigit()]
BURST_WINDOW = max(0, int(_env("BURST_WINDOW", "60") or 60))       # seconds either side of a mark
BURST_INTERVAL = max(2, int(_env("BURST_INTERVAL", "10") or 10))   # seconds between checks inside it
# Flag qmq's own feed as stale once its freshest row is older than this (minutes).
STALE_AFTER_MIN = float(_env("STALE_AFTER_MIN", "30") or 30)
NTFY_TOPIC = _env("NTFY_TOPIC")                      # ntfy.sh topic to publish to (REQUIRED for push)
NTFY_SERVER = _env("NTFY_SERVER", "https://ntfy.sh")
# Optional second channel: ntfy forwards a copy of an ALERT to this address.
# ntfy.sh rejects anonymous email sending ("code 40053"), so NTFY_TOKEN must
# hold an access token from a (free) ntfy account for this to work.
EMAIL_TO = _env("EMAIL")
NTFY_TOKEN = _env("NTFY_TOKEN")
STATE_FILE = Path(_env("STATE") or Path(__file__).with_name("state.json"))
# Append-only audit trail of every check (see check_and_notify).
HISTORY_FILE = Path(_env("HISTORY") or Path(__file__).with_name("history.jsonl"))
_today = _env("TODAY")
TODAY = dt.date.fromisoformat(_today) if _today else dt.date.today()


def current_today() -> dt.date:
    """Use calendar date in China's time zone; rollover during long --watch runs."""
    return TODAY if _today else dt.datetime.now(ZoneInfo("Asia/Shanghai")).date()


URL = "https://qmq.app"

# --------------------------------------------------------------------------- #
# DOM extraction: only trust CITY-ANCHORED availability panels. The "recent
# successful bookings" activity feed is NOT an appointment calendar.
# The extractor deliberately fails closed if no identifiable calendar exists.
# --------------------------------------------------------------------------- #
EXTRACT_JS = r"""
(citiesWanted) => {
  const CITY_NAMES = citiesWanted;
  const citySet = new Set(CITY_NAMES);
  const COUNT = /(?:\d[\d,]*\s*个可用日期|可用日期\s*[:：]?\s*\d[\d,]*|暂无可用日期|无可用日期|\d[\d,]*\s*available dates?)/i;
  const GRID_WORD = /可用日期|可预约日期|预约日历|面签日历|available dates?/i;
  const BADGE = /^(?:B1\/B2|B1|B2|F-1|F-2|J-1|H-1B|H1B|H-4|L-1|L-2|K-1|O-1|C1\/D|F1)(?=$|\s|[：:|•])/i;
  const DATE = /(?:20\d{2}[-\/.]\d{1,2}[-\/.]\d{1,2}|20\d{2}年\d{1,2}月\d{1,2}日|\d{1,2}月\d{1,2}日)/g;
  const UPDATED = /(刚刚|\d+\s*(?:秒|分钟|小时|天)前)更新/;
  const EMERGENCY = /官方紧急申请|不是普通号|emergency[- ]only/i;
  const STOP = /^(?:最近抢位成功|最新抢位成功|抢位成功记录|最近成功记录|成功案例|常见问题|FAQ|用户评价|新闻动态|最新动态)/;
  const normalize = s => (s || '').replace(/\u00a0/g, ' ').replace(/\s+/g, ' ').trim();
  const visible = e => {
    if (!e || !e.isConnected) return false;
    const style = getComputedStyle(e);
    return style.display !== 'none' && style.visibility !== 'hidden';
  };
  const text = e => (e && e.innerText) || '';
  const linesOf = s => (s || '').split(/\n+/).map(normalize).filter(Boolean);
  const cleanCity = s => CITY_NAMES.find(c => s === c || s.startsWith(c + ' ') || s.startsWith(c + '：') || s.startsWith(c + ':')) || null;
  const distinctCities = s => CITY_NAMES.filter(c => new RegExp('(?:^|\\n)\\s*' + c + '(?=\\s|$|[:：])').test(s));

  function parseRows(raw) {
    const ls = linesOf(raw);
    const heads = [];
    for (let i = 0; i < ls.length; i++) {
      const m = ls[i].match(BADGE);
      if (m) {
        const badge = m[0].replace(/H1B/i, 'H-1B').trim();
        // Old cards often render the badge and description on consecutive
        // lines: "H-1B" / "H-1B Visa ...". They form ONE row, not two.
        if (heads.length && heads[heads.length - 1].i === i - 1 &&
            ls[i - 1].trim().toUpperCase() === badge.toUpperCase() &&
            ls[i].length > badge.length && ls[i].slice(badge.length).trim()) {
          continue;
        }
        heads.push({i, badge});
      }
    }
    const rows = [];
    for (let k = 0; k < heads.length; k++) {
      const h = heads[k];
      if (h.badge.toUpperCase() !== 'H-1B') continue;
      const part = ls.slice(h.i, k + 1 < heads.length ? heads[k + 1].i : ls.length);
      let desc = part[0].replace(BADGE, '').replace(/^[\s:：|•-]+/, '').trim();
      if (!desc && part[1] && !/(?:20\d{2}[-\/.]\d{1,2}[-\/.]\d{1,2}|\d{1,2}月\d{1,2}日)/.test(part[1]) &&
          !/^(有位|紧缺|暂无|无位)$/.test(part[1])) desc = part[1];
      DATE.lastIndex = 0;
      const dates = [];
      for (const line of part) {
        // Skip update timestamps; accept only appointment-date-shaped labels.
        if (/前更新/.test(line)) continue;
        for (const m of line.matchAll(DATE)) dates.push(m[0]);
      }
      const status = part.find(x => /^(?:有位|紧缺|暂无|无位)$/.test(x)) || '?';
      rows.push({badge: 'H-1B', desc: desc || 'H-1B', status,
                 emergency: part.some(x => EMERGENCY.test(x)),
                 updated: part.find(x => UPDATED.test(x)) || '',
                 dates: [...new Set(dates)]});
    }
    return rows;
  }

  // Strategy A: find individually scoped city cards via calendar/count nodes.
  // Don't use document.body's entire text; it also contains a global activity feed.
  const cards = new Map();
  const candidates = [...document.querySelectorAll('button, [role="button"], h1, h2, h3, h4, div, section, article, span')]
    .filter(visible).filter(e => {
      const own = normalize(text(e));
      return own.length < 180 && COUNT.test(own);
    });
  for (const el of candidates) {
    let best = null;
    for (let cur = el, depth = 0; cur && depth < 7; cur = cur.parentElement, depth++) {
      const t = text(cur);
      if (t.length > 16000) break;
      const cities = distinctCities(t);
      // If two city headers appear, the container is no longer a single city card.
      if (cities.length > 1) break;
      if (cities.length === 1 && COUNT.test(t) && BADGE.test(linesOf(t).find(l => BADGE.test(l)) || '')) {
        best = {city: cities[0], element: cur};
        break;
      }
    }
    if (best && !cards.has(best.city)) cards.set(best.city, best.element);
  }

  // Strategy B: revised UI may put city panels under named headings without a
  // count button. Require a nearby calendar marker and a typed visa listing.
  if (cards.size < CITY_NAMES.length) {
    const headings = [...document.querySelectorAll('h1,h2,h3,h4,h5,[role="heading"],button,[role="tab"]')].filter(visible);
    for (const heading of headings) {
      const city = cleanCity(normalize(text(heading)));
      if (!city || cards.has(city)) continue;
      for (let cur = heading.parentElement, depth = 0; cur && depth < 5; cur = cur.parentElement, depth++) {
        const t = text(cur);
        if (t.length > 16000 || distinctCities(t).length > 1) break;
        const ls = linesOf(t);
        if (GRID_WORD.test(t) && ls.some(l => BADGE.test(l)) &&
            (ls.some(l => /H-1B|H1B/.test(l)) || COUNT.test(t))) {
          cards.set(city, cur);
          break;
        }
      }
    }
  }

  // Strategy C: legacy flat city grid with consecutive '<N> 个可用日期'
  // separators. This is accepted only if the count markers are present.
  if (cards.size < CITY_NAMES.length) {
    const source = text(document.querySelector('main') || document.body);
    const ls = linesOf(source);
    const starts = [];
    for (let i = 0; i < ls.length; i++) {
      if (!COUNT.test(ls[i])) continue;
      const city = cleanCity(ls[i]) || cleanCity(ls[i - 1] || '');
      if (city && citySet.has(city)) starts.push({city, i});
    }
    // Require at least two independently marked city sections to rule out a
    // single advertisement, user activity entry, or booking confirmation.
    if (starts.length >= 2) {
      starts.forEach((start, k) => {
        if (cards.has(start.city)) return;
        const end = k + 1 < starts.length ? starts[k + 1].i - 1 : ls.length;
        const seg = ls.slice(start.i + 1, end);
        const stopAt = seg.findIndex(x => STOP.test(x));
        const section = (stopAt >= 0 ? seg.slice(0, stopAt) : seg).join('\n');
        cards.set(start.city, {innerText: section});
      });
    }
  }

  const cities = CITY_NAMES.filter(c => cards.has(c)).map(city => {
    const raw = text(cards.get(city));
    const firstLines = linesOf(raw).slice(0, 5).join(' ');
    const count = firstLines.match(/(\d[\d,]*)\s*个可用日期|可用日期\s*[:：]?\s*(\d[\d,]*)/);
    return {city, count: count ? (count[1] || count[2]) : '', rows: parseRows(raw)};
  });
  const rowCount = cities.reduce((n, c) => n + c.rows.length, 0);
  if (!cities.length) return {error: 'city-calendar-not-found', cities: []};
  if (!rowCount && !(cities.length === CITY_NAMES.length &&
                     cities.every(c => c.count.replace(/,/g, '') === '0')))
    return {error: 'h1b-rows-not-found', cities};
  return {cities};
}
"""


def parse_age_minutes(txt: str):
    """'刚刚更新'->0, '8分钟前更新'->8, '2小时前更新'->120, '1天前更新'->1440.

    This is qmq's OWN staleness: how long ago they last refreshed that row. If
    it is hours, no polling rate on our side can see new slots -- the upstream
    feed simply is not publishing.
    """
    if not txt:
        return None
    if "刚刚" in txt:
        return 0.0
    mm = re.search(r"(\d+)\s*(秒|分钟|小时|天)前", txt)
    if not mm:
        return None
    return int(mm.group(1)) * {"秒": 1 / 60, "分钟": 1, "小时": 60, "天": 1440}[mm.group(2)]


def parse_cn_date(chip: str, today: dt.date) -> dt.date:
    """Parse calendar chips; never treat past dates as available appointments."""
    s = chip.strip()
    iso = re.fullmatch(r"(20\d{2})[-/.](\d{1,2})[-/.](\d{1,2})", s)
    full_cn = re.fullmatch(r"(20\d{2})年(\d{1,2})月(\d{1,2})日", s)
    if iso or full_cn:
        y, m, d = map(int, (iso or full_cn).groups())
        return dt.date(y, m, d)
    m = re.fullmatch(r"(\d{1,2})月(\d{1,2})日", s)
    if not m:
        raise ValueError(chip)
    month, day = map(int, m.groups())
    candidate = dt.date(today.year, month, day)
    return candidate if candidate >= today else dt.date(today.year + 1, month, day)


CF_MARKERS = ("Just a moment", "cf-browser-verification", "Attention Required",
              "Error 1015", "rate limited", "Checking your browser")


UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
      "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36")


def _new_page(browser):
    """A fresh context+page with a realistic locale/UA."""
    ctx = browser.new_context(locale="zh-CN", user_agent=UA)
    return ctx.new_page()




def _safe_endpoint(raw: str) -> str:
    """Log only an origin and redacted path; never log tokens or URL queries."""
    try:
        u = urllib.parse.urlsplit(raw)
        if u.scheme not in ('http', 'https', 'ws', 'wss'):
            return 'other-scheme'
        parts = []
        for part in u.path.split('/'):
            # Dynamic path components may contain bearer tokens, IDs, or emails.
            if '@' in part or len(part) > 42 or re.search(r'[A-Za-z0-9_-]{24,}', part):
                part = ':redacted'
            parts.append(part)
        return f'{u.scheme}://{u.netloc}' + '/'.join(parts)
    except Exception:
        return 'unparseable-endpoint'


def _diagnostic_snapshot(page, events: dict) -> None:
    """Only page *structure* and network metadata, never booking records/PII.

    The previous code printed the body text of qmq.app, which is a misleading
    source of homepage booking-success dates. This report avoids that entirely.
    """
    try:
        state = page.evaluate(r"""() => {
          const clean = t => (t || '').replace(/\s+/g, ' ').trim().slice(0, 70);
          const matches = t => /可用日期|预约日历|面签日历|实时日历|查号|号源|空位|签证|预约|calendar|availability|slot/i.test(t);
          const visible = e => !!e.getClientRects().length &&
            getComputedStyle(e).visibility !== 'hidden';
          const body = document.body?.innerText || '';
          const gather = (selector, limit = 18) =>
            [...document.querySelectorAll(selector)].filter(visible)
              .map(e => clean(e.innerText || e.textContent))
              .filter(t => t && matches(t)).slice(0, limit);
          const anchor = [...document.querySelectorAll('a[href]')]
            .filter(visible).map(e => ({label: clean(e.innerText),
              href: e.getAttribute('href') || ''}))
            .filter(x => matches(x.label)).slice(0, 15);
          const cities = ['广州','北京','上海','沈阳','武汉'];
          return {
            title: document.title, html_bytes: document.documentElement?.outerHTML.length || 0,
            visible_text_chars: body.length,
            document_ready_state: document.readyState,
            city_name_mentions_in_whole_page: Object.fromEntries(cities.map(c =>
              [c, (body.match(new RegExp(c, 'g')) || []).length])),
            has_count_labels: /\d[\d,]*\s*个可用日期/.test(body),
            has_calendar_words: /可用日期|预约日历|面签日历|calendar|availability/i.test(body),
            has_success_feed: /最近抢位成功|抢位成功记录|最近成功/i.test(body),
            h1b_mentions_in_whole_page: (body.match(/H-1B|H1B/gi)||[]).length,
            matched_headings: gather('h1,h2,h3,h4,h5,[role="heading"]'),
            matched_buttons_tabs: gather('button,[role="button"],[role="tab"]'),
            matched_links: anchor,
            iframe_count: document.querySelectorAll('iframe').length,
            script_count: document.querySelectorAll('script').length
          };
        }""")
        # A link may contain tokens or customer-specific query strings. Redact it.
        for item in state.get('matched_links', []):
            href = item.pop('href', '')
            item['path'] = _safe_endpoint(urllib.parse.urljoin(page.url, href))
        print('[diagnostic] page_structure=' + json.dumps(state, ensure_ascii=False), flush=True)
    except Exception as exc:
        print('[diagnostic] page_structure_unavailable=' + type(exc).__name__, flush=True)
    print('[diagnostic] transport=' + json.dumps(events, ensure_ascii=False), flush=True)
    if os.environ.get('VISA_DIAG_SCREENSHOT', '') == '1':
        try:
            dest = Path('qmq_failure.png')
            page.screenshot(path=str(dest), full_page=True, timeout=10_000)
            print('[diagnostic] screenshot_saved=' + str(dest), flush=True)
        except Exception as exc:
            print('[diagnostic] screenshot_failed=' + type(exc).__name__, flush=True)


def render_and_extract(page, today: dt.date) -> dict:
    """Find the real availability calendar, never infer dates from homepage news.

    Uses multiple DOM layouts and (optionally) follows a discovered calendar tab.
    If no calendar is published, fail explicitly instead of waiting forever on
    the old hard-coded 'N个可用日期' button selector.
    """
    from playwright.sync_api import TimeoutError as PWTimeout

    # Keep a bounded record of network *metadata*, never bodies or query params.
    events = {'xhr_fetch': [], 'failed_requests': [], 'websockets': [], 'js_errors': []}
    def on_response(response):
        try:
            kind = response.request.resource_type
            if kind in ('xhr', 'fetch', 'document') and len(events['xhr_fetch']) < 30:
                events['xhr_fetch'].append({
                    'type': kind, 'status': response.status,
                    'endpoint': _safe_endpoint(response.url)})
        except Exception:
            pass
    def on_requestfailed(request):
        if len(events['failed_requests']) < 15:
            events['failed_requests'].append({
                'type': request.resource_type,
                'endpoint': _safe_endpoint(request.url)})
    def on_websocket(ws):
        if len(events['websockets']) < 10:
            events['websockets'].append(_safe_endpoint(ws.url))
    def on_pageerror(exc):
        if len(events['js_errors']) < 8:
            # Don't log an exception message: it might embed an auth token.
            events['js_errors'].append(type(exc).__name__)
    listeners = [('response', on_response), ('requestfailed', on_requestfailed),
                 ('websocket', on_websocket), ('pageerror', on_pageerror)]
    for event, callback in listeners:
        page.on(event, callback)

    try:
        response = page.goto(URL, wait_until="domcontentloaded", timeout=45_000)
        status = response.status if response else None
        print(f"[debug] HTTP {status}; URL: {page.url}", flush=True)
        if status is not None and status >= 400:
            raise RuntimeError(f"http-{status}")
        body = page.locator('body').inner_text(timeout=10_000)
        if any(x.lower() in body.lower() for x in CF_MARKERS):
            raise RuntimeError('cloudflare')

        # The old grid may now live under a "日历" tab / link. We ONLY click a
        # link with an explicit calendar label; never click checkout/order/login.
        clicked_calendar = False
        deadline = time.monotonic() + 28
        last_error = 'city-calendar-not-found'
        while time.monotonic() < deadline:
            result = page.evaluate(EXTRACT_JS, CITIES)
            if not result.get('error') and len(result.get('cities', [])) == len(CITIES):
                print('[debug] Parsed H-1B calendar: ' +
                      ', '.join(f"{c['city']}={len(c['rows'])} rows" for c in result['cities']),
                      flush=True)
                return result
            last_error = result.get('error', 'missing-city-panels')

            if not clicked_calendar and time.monotonic() > deadline - 22:
                # Look for a real calendar link/button in the currently rendered
                # page, instead of guessing a URL or scraping recent success feeds.
                links = page.locator('a, button, [role="tab"]')
                targets = []
                for i in range(min(links.count(), 200)):
                    node = links.nth(i)
                    try:
                        label = (node.inner_text(timeout=250) or '').strip()
                    except PWTimeout:
                        continue
                    if re.search(r'预约日历|实时日历|可用日期|面签日历', label) and len(label) < 36:
                        targets.append((node, label))
                if len(targets) == 1:
                    try:
                        targets[0][0].click(timeout=3000)
                        print(f'[debug] Opened calendar control: {targets[0][1]}', flush=True)
                    except Exception as exc:
                        print('[debug] Calendar control not clickable:', type(exc).__name__, flush=True)
                clicked_calendar = True
            page.wait_for_timeout(1000)

        # Diagnose without dumping the global recent-bookings feed.
        result = page.evaluate(EXTRACT_JS, CITIES)
        present = [c['city'] for c in result.get('cities', [])]
        missing = [c for c in CITIES if c not in present]
        print(f'[debug] Calendar unavailable; recognized cities={present}, missing={missing}, '
              f'reason={result.get("error", last_error)}', flush=True)
        _diagnostic_snapshot(page, events)
        raise RuntimeError(f'calendar-unavailable ({last_error}; '
                           f'parsed {len(present)}/{len(CITIES)} cities)')
    except PWTimeout as exc:
        _diagnostic_snapshot(page, events)
        raise RuntimeError(f'page-navigation-or-render-timeout ({str(exc).splitlines()[0]})') from exc
    finally:
        for event, callback in listeners:
            page.remove_listener(event, callback)



def scrape(today: dt.date) -> dict:
    """One-shot: launch a browser, render+extract once, close."""
    from playwright.sync_api import sync_playwright
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, args=["--no-sandbox"])
        try:
            return render_and_extract(_new_page(browser), today)
        finally:
            browser.close()


def _desc_filter(city: str) -> str:
    """Description filter for a city: per-city override, else the global default."""
    return DESC_BY_CITY.get(city, DESC_CONTAINS)


# How to treat rows tagged 官方紧急申请 - 不是普通号 ("emergency-only" slots):
# Prefixed to a title whenever a date on/before the cutoff exists.
ALERT_MARK = "‼️"

EMG_EXCLUDE = "exclude"   # regular slots only  -> the "status" view and normal alerts
EMG_ONLY = "only"         # emergency slots only -> the "emergency status" view
EMG_INCLUDE = "include"   # both


def _row_wanted(row: dict, city: str = "", emergency: str | None = None) -> bool:
    """Only H-1B rows; never expand emergency status into F/J categories."""
    if city and city not in CITIES:
        return False
    if row.get('badge', '').upper() != 'H-1B':
        return False
    mode = emergency or (EMG_INCLUDE if INCLUDE_EMERGENCY else EMG_EXCLUDE)
    if mode == EMG_ONLY and not row.get('emergency'):
        return False
    if mode == EMG_EXCLUDE and row.get('emergency'):
        return False
    desc = _desc_filter(city) if city else DESC_CONTAINS
    return not desc or desc.lower() in row.get('desc', '').lower()


def _short_desc(desc: str) -> str:
    """'F-1 Student • Students - Graduate / PhD students' -> 'Graduate / PhD students'."""
    tail = desc.split("•")[-1].strip()
    return tail.replace("Students - ", "").strip() or desc


def target_label() -> str:
    """Human-readable description of what we're watching, incl. per-city rules."""
    parts = [VISA_PREFIX, f"[{DESC_CONTAINS or 'ALL'}]"]
    if DESC_BY_CITY:
        parts.append("(" + ", ".join(f"{c}={d or 'ALL'}" for c, d in DESC_BY_CITY.items()) + ")")
    return " ".join(parts)


def _cities_index(data: dict) -> dict:
    return {c["city"]: c for c in data.get("cities", [])}


def validate_snapshot(data: dict) -> None:
    """Never send alerts / update dedup state on a missing or partial calendar."""
    if data.get('error'):
        raise ValueError(data['error'])
    idx = _cities_index(data)
    missing = [c for c in CITIES if c not in idx]
    if missing:
        raise ValueError('missing city panels: ' + ', '.join(missing))
    # A city with 0 *total* available dates may legitimately show no H-1B row.
    # Otherwise no typed row means we cannot establish the H-1B status.
    unknown = [c for c in CITIES if not any(_row_wanted(r, c, EMG_INCLUDE)
                                               for r in idx[c].get('rows', []))
               and str(idx[c].get('count', '')).replace(',', '') != '0']
    if unknown:
        raise ValueError('H-1B listing missing/unknown: ' + ', '.join(unknown))


def find_matches(data: dict, today: dt.date, cutoff: dt.date) -> list[dict]:
    """Across the wanted CITIES, return matching rows (>=1 date on/before cutoff)."""
    matches = []
    idx = _cities_index(data)
    for city in CITIES:
        c = idx.get(city)
        if not c:
            continue
        for row in c["rows"]:
            if not _row_wanted(row, city):
                continue
            hits = []
            for chip in row["dates"]:
                try:
                    d = parse_cn_date(chip, today)
                except ValueError:
                    continue
                if today <= d <= cutoff:
                    hits.append(d.isoformat())
            if hits:
                matches.append({"city": city, "badge": row["badge"], "desc": row["desc"],
                                "status": row["status"], "emergency": row.get("emergency", False),
                                "dates": sorted(set(hits))})
    return matches


def load_state() -> dict:
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text())
        except Exception:
            return {}
    return {}


def save_state(state: dict) -> None:
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2))


def push(title: str, body: str, click: str = URL, priority: str = "urgent",
         email: str = "") -> None:
    if not NTFY_TOPIC:
        print("[warn] VISA_NTFY_TOPIC not set -- skipping push. Message was:\n", title, body)
        return
    headers = {
        "Title": title.encode("utf-8").decode("latin-1", "ignore"),
        "Priority": priority,
        "Click": click,
    }
    if email:
        headers["Email"] = email          # ntfy forwards a copy by e-mail
    if NTFY_TOKEN:
        headers["Authorization"] = f"Bearer {NTFY_TOKEN}"
    req = urllib.request.Request(
        f"{NTFY_SERVER}/{urllib.parse.quote(NTFY_TOPIC)}",
        data=body.encode("utf-8"),
        headers=headers,
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=20) as r:
        r.read()


def push_repeated(title: str, body: str, click: str = URL) -> None:
    """Send the same alert PUSH_REPEAT times, PUSH_INTERVAL seconds apart, so an
    alert is hard to overlook. Each copy is numbered (i/N). Failures don't abort."""
    if not NTFY_TOPIC:
        push(title, body, click)  # prints the "not set" warning once
        return
    for i in range(PUSH_REPEAT):
        suffix = f" ({i + 1}/{PUSH_REPEAT})" if PUSH_REPEAT > 1 else ""
        # Only the FIRST copy carries the e-mail header -- one e-mail per alert,
        # not one per repeat.
        email = EMAIL_TO if i == 0 else ""
        try:
            push(title + suffix, body, click, email=email)
        except Exception as e:
            print(f"[push] copy {i + 1}/{PUSH_REPEAT} failed: {e}", flush=True)
            if email:
                # E-mail forwarding can fail on its own (no ntfy account/token,
                # quota). It must never take the actual alert down with it.
                print("[push] retrying copy 1 without e-mail forwarding", flush=True)
                try:
                    push(title + suffix, body, click)
                except Exception as e2:
                    print(f"[push] retry also failed: {e2}", flush=True)
        if i < PUSH_REPEAT - 1:
            time.sleep(PUSH_INTERVAL)


def check_and_notify(data: dict, verbose: bool = True) -> None:
    """Given extracted data: log status, and push on genuinely NEW qualifying dates."""
    cutoff = dt.date.fromisoformat(CUTOFF)
    stamp = dt.datetime.now().isoformat(timespec="seconds")

    validate_snapshot(data)

    idx = _cities_index(data)
    found = [c for c in CITIES if c in idx]
    missing = [c for c in CITIES if c not in idx]
    note = f"parsed {len(found)}/{len(CITIES)} cities" + (f"; MISSING {','.join(missing)}" if missing else "")
    # How stale is qmq's OWN data? If their freshest row is hours old they are
    # not publishing, and no polling rate of ours can surface a new slot.
    ages = []
    for c in data.get("cities", []):
        if c["city"] not in CITIES:
            continue
        for r in c["rows"]:
            a = parse_age_minutes(r.get("updated", ""))
            if a is not None:
                ages.append(a)
    freshest = min(ages) if ages else None
    if freshest is None:
        age_note = ""
    elif freshest >= STALE_AFTER_MIN:
        age_note = f"; qmq data STALE (freshest row {freshest / 60:.1f}h old)"
    else:
        age_note = f"; qmq freshest {freshest:.0f}m"
    print(f"[{stamp}] STATUS: OK ({note}{age_note})", flush=True)
    _, status_body = build_status(data, EMG_EXCLUDE)
    print(f"[{stamp}] H-1B earliest regular appointments:\n" +
          "\n".join("    " + x for x in status_body.splitlines()), flush=True)

    matches = find_matches(data, current_today(), cutoff)
    # Fingerprint keyed by city+category so alerts are per-city and dedup correctly.
    fp = {f"{m['city']} · {m['desc']}": m["dates"] for m in matches}

    state = load_state()
    prev = state.get("last_matches", {})

    # New qualifying dates = anything present now that wasn't alerted before.
    new_hits = {}
    for key, dates in fp.items():
        fresh = [d for d in dates if d not in prev.get(key, [])]
        if fresh:
            new_hits[key] = fresh

    target = target_label()
    if verbose:
        if matches:
            print(f"[{stamp}] {target} MATCHES by {cutoff}:")
            for m in matches:
                emg = " ⚠emergency-only" if m.get("emergency") else ""
                print(f"    {m['city']} {m['badge']} ({m['desc']}) [{m['status']}]{emg}: {', '.join(m['dates'])}")
        else:
            print(f"[{stamp}] {target}: no qualifying date by {cutoff}.", flush=True)

    if new_hits:
        # Summarize matching availability per LOCATION: earliest date + count of
        # qualifying dates (not every date). Locations sorted earliest-first.
        by_city: dict[str, dict] = {}
        for m in matches:
            e = by_city.setdefault(m["city"], {"dates": set(), "descs": set()})
            e["dates"].update(m["dates"])
            e["descs"].add(m["desc"])
        summary = sorted(((c, sorted(e["dates"]), e["descs"]) for c, e in by_city.items()),
                         key=lambda t: t[1][0])
        lines = []
        for c, ds, descs in summary:
            plural = "" if len(ds) == 1 else "s"
            # Cities watched across several sub-categories (per-city override) also
            # name which category opened -- otherwise the alert is ambiguous.
            cats = ""
            if c in DESC_BY_CITY:
                cats = " (" + ", ".join(sorted(_short_desc(d) for d in descs)) + ")"
            lines.append(f"{c}: earliest {ds[0]}, {len(ds)} date{plural}{cats}")
        loc = f"{len(summary)} location{'' if len(summary) == 1 else 's'}"
        # An alert only fires because a date qualified, so it always leads with ‼️.
        title = f"{ALERT_MARK} {VISA_PREFIX} · {loc} by {CUTOFF}"
        body = "\n".join(lines)
        push_repeated(title, body)
        print(f"[{stamp}] PUSHED x{PUSH_REPEAT} (every {PUSH_INTERVAL}s): " + " | ".join(lines))

    # Tell the user when the upstream feed recovers. While qmq is frozen we
    # cannot see new slots at all, so "source is live again" is itself news.
    was_stale = bool(state.get("src_stale"))
    is_stale = freshest is not None and freshest >= STALE_AFTER_MIN
    if was_stale and freshest is not None and not is_stale:
        push(f"{VISA_PREFIX} source is LIVE again",
             f"qmq data is fresh again (freshest row {freshest:.0f}m old).\n"
             f"Slot monitoring is effective from now on.", priority="high")
        print(f"[{stamp}] SOURCE RECOVERED (age {freshest:.0f}m) -- notified", flush=True)
    elif is_stale and not was_stale:
        push(f"{VISA_PREFIX} source went STALE",
             f"qmq has stopped publishing (freshest row {freshest / 60:.1f}h old).\n"
             f"New slots cannot be detected until it recovers.", priority="default")
        print(f"[{stamp}] SOURCE WENT STALE (age {freshest:.0f}m) -- notified", flush=True)
    if freshest is not None:
        state["src_stale"] = is_stale

    # Persist current qualifying set so we only alert on genuinely new dates.
    state["last_matches"] = fp
    state["last_checked"] = stamp
    save_state(state)

    # Durable audit trail: one compact line per check. watch.log can be rotated
    # or truncated; this is what lets you reconstruct "what did we see at time
    # T?" after a suspected miss.
    try:
        snapshot = {}
        for c in data.get("cities", []):
            if c["city"] not in CITIES:
                continue
            # Audit only the five configured cities and H-1B listings.
            snapshot[c["city"]] = {
                f"{r['badge']} {_short_desc(r['desc'])}" + ("!" if r.get("emergency") else ""):
                    r["dates"][:3]
                for r in c["rows"] if r["dates"] and _row_wanted(r, c['city'], EMG_INCLUDE)
            }
        line = json.dumps({"t": stamp, "matched": fp, "src_age_min": freshest,
                           "seen": snapshot}, ensure_ascii=False)
        with HISTORY_FILE.open("a") as fh:
            fh.write(line + "\n")
    except Exception:
        pass  # auditing must never break monitoring


def parse_command(text: str) -> str | None:
    """Map an inbound ntfy message to a status request.

    "status"           -> EMG_EXCLUDE: regular slots only
    "emergency status" -> EMG_ONLY:    官方紧急申请 - 不是普通号 slots only
    anything else      -> None (ignore)
    """
    t = " ".join((text or "").strip().lower().split())
    if t in ("status", "check", "s"):
        return EMG_EXCLUDE
    if t in ("emergency status", "status emergency", "emergency", "es"):
        return EMG_ONLY
    return None


# Commands arrive on a background thread but must be executed on the main thread:
# Playwright's sync API is not thread-safe, so the listener only enqueues.
COMMANDS: "queue.Queue[str]" = queue.Queue()


def listen_for_commands() -> None:
    """Background thread: watch our own ntfy topic and enqueue status commands.

    ntfy streams the topic as newline-delimited JSON. We only react to plain
    messages with NO title -- every push we send has a title, so the bot can
    never answer itself and loop.
    """
    if not NTFY_TOPIC:
        return
    # No `since=` -- that default means "stream messages from now on". (Passing
    # since=now is rejected with HTTP 400; valid values are a duration/id/all.)
    url = f"{NTFY_SERVER}/{urllib.parse.quote(NTFY_TOPIC)}/json"
    while True:
        try:
            with urllib.request.urlopen(url) as stream:
                for raw in stream:
                    try:
                        msg = json.loads(raw.decode("utf-8", "replace"))
                    except ValueError:
                        continue
                    if msg.get("event") != "message" or msg.get("title"):
                        continue  # keepalive/open event, or one of our own pushes
                    mode = parse_command(msg.get("message", ""))
                    if mode is None:
                        continue
                    stamp = dt.datetime.now().isoformat(timespec="seconds")
                    print(f"[{stamp}] COMMAND: {msg.get('message', '').strip()!r} -> {mode}", flush=True)
                    COMMANDS.put(mode)
        except Exception:
            pass  # network blip / stream closed -- reconnect after a pause
        time.sleep(5)


def build_status(data: dict, emergency: str = EMG_EXCLUDE) -> tuple[str, str]:
    """On-demand status: the earliest slot at EACH watched location.

    Unlike the alert path this ignores the cutoff (so it still tells you
    something when nothing qualifies); dates at/below the cutoff are marked ✓.
    `emergency=EMG_ONLY` reports ONLY 官方紧急申请 - 不是普通号 rows; the default
    reports only regular ones. The per-city category rules apply either way.
    """
    cutoff = dt.date.fromisoformat(CUTOFF)
    idx = _cities_index(data)
    lines: list[tuple[dt.date | None, str]] = []
    for city in CITIES:
        c = idx.get(city)
        if not c:
            lines.append((None, f"{city}: not found"))
            continue
        dates, labels = set(), set()
        for row in c["rows"]:
            if not _row_wanted(row, city, emergency):
                continue
            for chip in row["dates"]:
                try:
                    date = parse_cn_date(chip, current_today())
                    if date >= current_today():
                        dates.add(date)
                except ValueError:
                    continue
            if row["dates"]:
                # Keep labels optional; this monitor covers all H-1B subcategories.
                labels.add(row["badge"] if emergency == EMG_ONLY
                           else _short_desc(row["desc"]) if city in DESC_BY_CITY else "")
        if not dates:
            lines.append((None, f"{city}: none shown"))
            continue
        earliest = min(dates)
        named = sorted(x for x in labels if x)
        cats = f" ({', '.join(named)})" if named else ""
        mark = " ✓" if earliest <= cutoff else ""
        plural = "" if len(dates) == 1 else "s"
        lines.append((earliest, f"{city}: {earliest.isoformat()}, {len(dates)} date{plural}{cats}{mark}"))
    # Preserve requested city order rather than sorting the five consulates.
    hits = sum(1 for d, _ in lines if d and d <= cutoff)
    # The emergency view remains H-1B-only in this specialized monitor.
    if emergency == EMG_ONLY:
        what = f"H-1B emergency status (官方紧急申请 only)"
    elif emergency == EMG_INCLUDE:
        what = f"{VISA_PREFIX} status (regular + emergency)"
    else:
        what = f"{VISA_PREFIX} status"
    # Lead with ‼️ whenever something is actually on/before the cutoff, so a
    # hit is obvious from the notification title alone.
    title = (f"{ALERT_MARK} {what} · {hits} at/before {CUTOFF}" if hits
             else f"{what} · none by {CUTOFF}")
    return title, "\n".join(text for _, text in lines)


def run_check(emergency: str = EMG_EXCLUDE, page=None) -> int:
    """On-demand: push a snapshot of the earliest slot per location.

    `page` lets the watch loop reuse its open browser instead of launching a
    second Chromium just to answer a command.
    """
    stamp = dt.datetime.now().isoformat(timespec="seconds")
    try:
        data = render_and_extract(page, current_today()) if page is not None else scrape(current_today())
        validate_snapshot(data)
    except Exception as e:
        reason = str(e) or e.__class__.__name__
        print(f"[{stamp}] STATUS: SCRAPE_FAILED ({reason})", flush=True)
        push(f"{VISA_PREFIX} status unavailable", f"Could not read qmq.app: {reason}",
             priority="default")
        return 1
    title, body = build_status(data, emergency)
    print(f"[{stamp}] {title}\n" + "\n".join("    " + b for b in body.split("\n")), flush=True)
    # single, non-urgent push: this is user-requested, not a slot alert. Does not
    # touch dedup state, so it can never suppress a real alert.
    push(title, body, priority="default")
    return 0


def run_once() -> int:
    try:
        data = scrape(current_today())
        validate_snapshot(data)
        check_and_notify(data)
        return 0
    except Exception as e:
        stamp = dt.datetime.now().isoformat(timespec="seconds")
        reason = str(e) or e.__class__.__name__
        print(f"[{stamp}] STATUS: SCRAPE_FAILED ({reason}) -- no valid H-1B data", flush=True)
        return 1   # red GitHub Actions run: failure should not masquerade as success


def in_burst_window(now: dt.datetime) -> bool:
    """True when within BURST_WINDOW seconds of a slot-release mark (:00/:30).

    Distance is measured around the hour, so :59:30 correctly counts as near
    the :00 mark.
    """
    if not BURST_MARKS:
        return False
    secs = now.minute * 60 + now.second
    for mark in BURST_MARKS:
        diff = abs(secs - mark * 60)
        if min(diff, 3600 - diff) <= BURST_WINDOW:
            return True
    return False


def run_watch(interval: int, recycle: int = 40) -> int:
    """Keep ONE browser open and re-check every ~`interval` seconds (near real-time).

    The site does not live-update its DOM, so each cycle reloads the page. A
    transient Cloudflare block / timeout just skips that cycle. Needs an
    always-on machine (your Mac or a small VPS). Ctrl-C to stop.
    """
    from playwright.sync_api import sync_playwright
    # Treat SIGTERM (how launchd/systemd stop us) like Ctrl-C so `finally`
    # runs and Chromium is closed cleanly instead of orphaned.
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    # Answer "status" / "emergency status" messages sent to our ntfy topic.
    threading.Thread(target=listen_for_commands, daemon=True).start()
    print(f"[watch] every ~{interval}s: {'/'.join(CITIES)} {target_label()} by {CUTOFF}. "
          f"Ctrl-C to stop.", flush=True)
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, args=["--no-sandbox"])
        page = _new_page(browser)
        n = 0
        try:
            was_hot = False
            while True:
                n += 1
                started = time.monotonic()
                try:
                    data = render_and_extract(page, current_today())
                    validate_snapshot(data)
                    check_and_notify(data)
                except Exception as e:
                    stamp = dt.datetime.now().isoformat(timespec="seconds")
                    reason = str(e) or e.__class__.__name__
                    print(f"[{stamp}] STATUS: SCRAPE_FAILED ({reason})", flush=True)
                # Periodically recycle the browser context to bound memory.
                if n % recycle == 0:
                    try:
                        page.context.close()
                    except Exception:
                        pass
                    page = _new_page(browser)
                # Near a release mark, poll fast; otherwise use the normal
                # interval (with jitter so we aren't perfectly periodic).
                hot = in_burst_window(dt.datetime.now())
                if hot != was_hot:
                    print(f"[watch] {'ENTERING' if hot else 'leaving'} burst mode "
                          f"({BURST_INTERVAL}s cadence)", flush=True)
                    was_hot = hot
                gap = BURST_INTERVAL if hot else interval + random.uniform(0, min(15, interval * 0.25))
                # Measure from the START of the check so a slow render eats into
                # the wait rather than stretching the cadence.
                deadline = started + gap
                # Idle until then, but stay responsive to commands: poll the
                # queue and answer on THIS thread (Playwright isn't thread-safe).
                while True:
                    left = deadline - time.monotonic()
                    if left <= 0:
                        break
                    try:
                        mode = COMMANDS.get(timeout=min(1.0, left))
                    except queue.Empty:
                        continue
                    try:
                        run_check(emergency=mode, page=page)
                    except Exception as e:
                        print(f"[command] failed: {e}", flush=True)
        except KeyboardInterrupt:
            print("\n[watch] stopped.", flush=True)
        finally:
            browser.close()
    return 0


def main() -> None:
    ap = argparse.ArgumentParser(description="visaMonitor -- US visa appointment availability monitor")
    ap.add_argument("--once", action="store_true", help="check a single time and exit (default)")
    ap.add_argument("--watch", nargs="?", type=int, const=60, metavar="SECONDS",
                    help="stay running, re-check every SECONDS (default 60, min 20); "
                         "near real-time, needs an always-on machine")
    ap.add_argument("--check", action="store_true",
                    help="on-demand: push the earliest slot at each watched location "
                         "(ignores the cutoff) and exit")
    ap.add_argument("--emergency", action="store_true",
                    help="with --check: report ONLY 官方紧急申请 - 不是普通号 slots "
                         "(default reports only regular ones)")
    ap.add_argument("--test-push", action="store_true", help="send a test push and exit")
    args = ap.parse_args()

    if args.test_push:
        push("visaMonitor test",
             f"Monitoring {VISA_PREFIX} [{DESC_CONTAINS}] in {'/'.join(CITIES)} for dates by {CUTOFF}.")
        print("test push sent (if VISA_NTFY_TOPIC set)")
        return

    if args.check:
        sys.exit(run_check(emergency=EMG_ONLY if args.emergency else EMG_EXCLUDE))

    if args.watch is not None:
        sys.exit(run_watch(max(20, args.watch)))

    sys.exit(run_once())


if __name__ == "__main__":
    main()
