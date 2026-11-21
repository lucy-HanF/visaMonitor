
#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
visaMonitor - H-1B China 5 Consulates Monitor

Monitors confirmed appointment dates for H-1B at:
Beijing, Shanghai, Guangzhou, Shenyang, Wuhan.

IMPORTANT:
VISA_DATA_URL must point to an authorized JSON data source.
This program does NOT interpret qmq's undocumented binary cal-view payload.
It deliberately refuses to treat homepage success records as availability.

Expected JSON schema:

{
  "cities": [
    {
      "city": "北京",
      "rows": [
        {
          "badge": "H-1B",
          "dates": ["2026-12-15", "2027-01-10"],
          "status": "有位"
        }
      ]
    }
  ]
}
"""

import argparse
import datetime as dt
import json
import os
import sys
import time
import urllib.request
import urllib.error
from pathlib import Path

# ============================================================
# FIXED MONITOR CONFIGURATION
# ============================================================

CITIES = ["北京", "上海", "广州", "沈阳", "武汉"]
VISA_TYPE = "H-1B"

CUTOFF = os.getenv("VISA_CUTOFF", "").strip()

if CUTOFF:
    CUTOFF_DATE = dt.date.fromisoformat(CUTOFF)
else:
    CUTOFF_DATE = dt.date.today() + dt.timedelta(days=60)

# Authorized JSON endpoint - REQUIRED
DATA_URL = os.getenv("VISA_DATA_URL", "").strip()

# Optional bearer token, only for an endpoint you are authorized to access.
DATA_TOKEN = os.getenv("VISA_DATA_TOKEN", "").strip()

# ntfy
NTFY_TOPIC = os.getenv("VISA_NTFY_TOPIC", "").strip()
NTFY_SERVER = os.getenv(
    "VISA_NTFY_SERVER", "https://ntfy.sh"
).rstrip("/")

NTFY_TOKEN = os.getenv("VISA_NTFY_TOKEN", "").strip()

PUSH_REPEAT = max(
    1, int(os.getenv("VISA_PUSH_REPEAT", "3"))
)

PUSH_INTERVAL = max(
    0, int(os.getenv("VISA_PUSH_INTERVAL", "5"))
)

# Files
BASE_DIR = Path(__file__).resolve().parent

STATE_FILE = Path(
    os.getenv("VISA_STATE", str(BASE_DIR / "state.json"))
)

HISTORY_FILE = Path(
    os.getenv("VISA_HISTORY", str(BASE_DIR / "history.jsonl"))
)

REQUEST_TIMEOUT = 30

# ============================================================
# DATA FETCH
# ============================================================

def fetch_data():
    """
    Fetch authorized JSON appointment data.

    This intentionally does not scrape the homepage's
    recent-success feed.
    """

    if not DATA_URL:
        raise RuntimeError(
            "VISA_DATA_URL is not configured. "
            "A verified appointment JSON endpoint is required."
        )

    if not DATA_URL.startswith("https://"):
        raise RuntimeError(
            "VISA_DATA_URL must use HTTPS."
        )

    headers = {
        "Accept": "application/json",
        "User-Agent": "visaMonitor-H1B/2.0"
    }

    if DATA_TOKEN:
        headers["Authorization"] = (
            f"Bearer {DATA_TOKEN}"
        )

    req = urllib.request.Request(
        DATA_URL,
        headers=headers,
        method="GET"
    )

    with urllib.request.urlopen(
        req, timeout=REQUEST_TIMEOUT
    ) as response:

        if response.status != 200:
            raise RuntimeError(
                f"Data source HTTP {response.status}"
            )

        raw = response.read()

    try:
        data = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeError(
            "Data source did not return valid UTF-8 JSON."
        ) from exc

    if not isinstance(data, dict):
        raise RuntimeError("Invalid JSON root.")

    return data


# ============================================================
# DATA VALIDATION AND NORMALIZATION
# ============================================================

def normalize_data(data):
    """
    Validate all five cities.

    Expected structure:
    {
        "cities": [
            {
                "city": "北京",
                "rows": [
                    {
                        "badge": "H-1B",
                        "dates": ["2026-12-15"]
                    }
                ]
            }
        ]
    }

    Only exact H-1B rows are accepted.
    """

    if not isinstance(data.get("cities"), list):
        raise RuntimeError(
            "JSON schema error: cities must be a list."
        )

    result = {}

    for city_data in data["cities"]:

        if not isinstance(city_data, dict):
            continue

        city = str(
            city_data.get("city", "")
        ).strip()

        if city not in CITIES:
            continue

        if city in result:
            raise RuntimeError(
                f"Duplicate city entry: {city}"
            )

        rows = city_data.get("rows")

        if not isinstance(rows, list):
            raise RuntimeError(
                f"Invalid rows structure for {city}"
            )

        valid_dates = set()

        for row in rows:

            if not isinstance(row, dict):
                continue

            badge = str(
                row.get("badge", "")
            ).strip()

            # Exact H-1B only.
            if badge != VISA_TYPE:
                continue

            dates = row.get("dates", [])

            if not isinstance(dates, list):
                raise RuntimeError(
                    f"Invalid dates for {city} H-1B"
                )

            for value in dates:

                try:
                    date = dt.date.fromisoformat(
                        str(value).strip()
                    )
                except ValueError:
                    raise RuntimeError(
                        f"Invalid ISO date: {value}"
                    )

                valid_dates.add(date.isoformat())

        result[city] = sorted(valid_dates)

    missing = [
        city for city in CITIES
        if city not in result
    ]

    if missing:
        raise RuntimeError(
            "Incomplete source data. Missing cities: "
            + ", ".join(missing)
        )

    return result


# ============================================================
# STATE MANAGEMENT
# ============================================================

def load_state():

    if not STATE_FILE.exists():
        return {}

    try:
        data = json.loads(
            STATE_FILE.read_text(encoding="utf-8")
        )

        if isinstance(data, dict):
            return data

    except Exception:
        print("[warn] Invalid state.json; starting fresh.")

    return {}


def save_state(state):

    STATE_FILE.parent.mkdir(
        parents=True, exist_ok=True
    )

    temp = STATE_FILE.with_suffix(".tmp")

    temp.write_text(
        json.dumps(
            state,
            ensure_ascii=False,
            indent=2
        ),
        encoding="utf-8"
    )

    temp.replace(STATE_FILE)


# ============================================================
# NTFY PUSH
# ============================================================

def push(title, message, priority="urgent"):

    if not NTFY_TOPIC:
        print(
            "[warn] VISA_NTFY_TOPIC not configured."
        )
        print(title)
        print(message)
        return

    headers = {
        "Title": title,
        "Priority": priority,
        "Content-Type": "text/plain; charset=utf-8"
    }

    if NTFY_TOKEN:
        headers["Authorization"] = (
            f"Bearer {NTFY_TOKEN}"
        )

    url = (
        f"{NTFY_SERVER}/"
        f"{NTFY_TOPIC}"
    )

    req = urllib.request.Request(
        url,
        data=message.encode("utf-8"),
        headers=headers,
        method="POST"
    )

    with urllib.request.urlopen(
        req, timeout=20
    ) as response:

        if response.status not in (200, 201):
            raise RuntimeError(
                f"ntfy HTTP {response.status}"
            )


def push_repeated(title, message):

    for i in range(PUSH_REPEAT):

        try:
            push(
                f"{title} ({i + 1}/{PUSH_REPEAT})",
                message
            )

            print(
                f"[push] sent {i + 1}/{PUSH_REPEAT}"
            )

        except Exception as exc:

            print(
                f"[push] failed: {exc}"
            )

        if i < PUSH_REPEAT - 1:
            time.sleep(PUSH_INTERVAL)


# ============================================================
# AVAILABILITY CHECK
# ============================================================

def check_availability(city_dates):

    today = dt.date.today()

    state = load_state()

    previous = state.get(
        "last_matches", {}
    )

    current = {}
    new_hits = {}

    print()
    print("=" * 55)
    print("visaMonitor - H-1B availability")
    print("Date:", today.isoformat())
    print("Cutoff:", CUTOFF_DATE.isoformat())
    print("=" * 55)

    for city in CITIES:

        dates = sorted(
            d for d in city_dates[city]
            if today <= dt.date.fromisoformat(d)
        )

        qualifying = [
            d for d in dates
            if dt.date.fromisoformat(d) <= CUTOFF_DATE
        ]

        current[city] = qualifying

        if dates:

            print(
                f"{city} H-1B: "
                f"earliest={dates[0]}, "
                f"total={len(dates)}"
            )

        else:

            print(
                f"{city} H-1B: no dates"
            )

        old_dates = set(
            previous.get(city, [])
        )

        fresh = [
            d for d in qualifying
            if d not in old_dates
        ]

        if fresh:
            new_hits[city] = fresh

    # Notify only newly discovered qualifying dates.
    if new_hits:

        lines = []

        for city in CITIES:

            if city not in new_hits:
                continue

            dates = new_hits[city]

            lines.append(
                f"{city}: {', '.join(dates)}"
            )

        title = (
            f"H-1B NEW SLOT - "
            f"{len(new_hits)} cities"
        )

        body = (
            "New H-1B appointment dates detected.\n\n"
            + "\n".join(lines)
            + f"\n\nCutoff: {CUTOFF_DATE.isoformat()}"
            + "\n\nPlease verify availability on the official appointment system."
        )

        push_repeated(title, body)

    else:

        print(
            "[status] No new qualifying H-1B dates."
        )

    # Save current qualifying dates.
    state["last_matches"] = current

    state["last_checked"] = (
        dt.datetime.now(
            dt.timezone.utc
        ).isoformat()
    )

    save_state(state)

    # Append-only audit history.
    HISTORY_FILE.parent.mkdir(
        parents=True, exist_ok=True
    )

    record = {
        "checked_at": state["last_checked"],
        "visa_type": VISA_TYPE,
        "cutoff": CUTOFF_DATE.isoformat(),
        "cities": city_dates,
        "qualifying": current,
        "new_hits": new_hits
    }

    with HISTORY_FILE.open(
        "a", encoding="utf-8"
    ) as f:

        f.write(
            json.dumps(
                record,
                ensure_ascii=False
            ) + "\n"
        )

    print("[status] Check completed.")
    print("=" * 55)


# ============================================================
# MAIN
# ============================================================

def main():

    parser = argparse.ArgumentParser(
        description="H-1B China five-consulate monitor"
    )

    parser.add_argument(
        "--once",
        action="store_true",
        help="Run one availability check."
    )

    parser.add_argument(
        "--test-push",
        action="store_true",
        help="Send a test ntfy notification."
    )

    parser.add_argument(
        "--check",
        action="store_true",
        help="Display the current H-1B availability."
    )

    args = parser.parse_args()

    if args.test_push:

        push(
            "visaMonitor test",
            "H-1B five-consulate notification test.\n"
            + "\n".join(CITIES),
            priority="default"
        )

        print("[status] Test push completed.")
        return

    try:

        print("[status] Fetching authorized calendar data...")

        raw = fetch_data()

        print("[status] Validating JSON data...")

        normalized = normalize_data(raw)

        check_availability(normalized)

    except urllib.error.HTTPError as exc:

        print(
            f"[error] Data source HTTP {exc.code}: {exc.reason}"
        )

        sys.exit(1)

    except Exception as exc:

        print(
            f"[error] Monitoring failed: {exc}"
        )

        # Do not overwrite state when data extraction fails.
        sys.exit(1)


if __name__ == "__main__":
    main()
