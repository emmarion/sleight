#!/bin/sh
set -eu
T=$(cd "$(dirname "$0")" && pwd)
B="$T/build"
CH=${CHROME:-"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"}
guard() { "$@" & pid=$!; for _ in $(seq 90); do kill -0 $pid 2>/dev/null || return 0; sleep 1; done; kill $pid; echo "timed out: $1" >&2; exit 1; }
if [ "${1:-}" = charts ] || [ ! -f "$T/chart/heapsort-runs.png" ] || [ ! -f "$T/chart/certified-sorts.png" ]; then
  (cd "$T/chart" && python3 make_runs.py "$T/../heapsort/agent-runs-8860c75.csv" heapsort-runs.svg && python3 make_langs.py certified-sorts.svg)
  guard "$CH" --headless --disable-gpu --hide-scrollbars --force-device-scale-factor=2 --window-size=1800,680 --screenshot="$T/chart/heapsort-runs.png" "file://$T/chart/heapsort-runs.svg" >/dev/null 2>&1
  guard "$CH" --headless --disable-gpu --hide-scrollbars --force-device-scale-factor=2 --window-size=1800,800 --screenshot="$T/chart/certified-sorts.png" "file://$T/chart/certified-sorts.svg" >/dev/null 2>&1
fi
[ -x "$B/node_modules/.bin/marp" ] || (cd "$B" && npm install --silent)
cd "$B"
python3 to_marp.py ../slides.md slides.marp.md
guard ./node_modules/.bin/marp --allow-local-files --html slides.marp.md -o slides.html >/dev/null 2>&1
python3 inject.py
guard "$CH" --headless --disable-gpu --window-size=1280,720 --virtual-time-budget=5000 --dump-dom "file://$B/measure.html" > dom.html 2>/dev/null
python3 report.py
guard "$CH" --headless --disable-gpu --no-pdf-header-footer --virtual-time-budget=10000 --run-all-compositor-stages-before-draw --print-to-pdf="$T/slides.pdf" "file://$B/print.html" >/dev/null 2>&1
echo "wrote $T/slides.pdf"
