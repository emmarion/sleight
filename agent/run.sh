#!/bin/bash
set -eu
usage() {
    echo "usage: $0 IP PI-ARGS...   deploy HEAD, then start pi.py PI-ARGS (paths relative to agent/) in tmux session pi, passing on PI_* variables" >&2
    echo "       $0 status IP      list the runs on the box" >&2
    echo "       $0 fetch IP       copy the box's results into agent/results/box-IP/" >&2
    exit 2
}
cd "$(dirname "$0")/.."
SSH="ssh -o BatchMode=yes -o StrictHostKeyChecking=accept-new"
case "${1:-}" in
status | fetch) cmd=$1; shift ;;
*) cmd=start ;;
esac
[ $# -ge 1 ] || usage
IP=$1
shift

case $cmd in
start)
    [ $# -ge 1 ] || usage
    agent/deploy.sh "$IP"
    log=results/$($SSH pi@"$IP" date +%Y%m%d-%H%M%S).log
    vars=$(env | grep -E '^PI_' | grep -vE '^PI_(SLC|DEPLOY_ENV)=' || true)
    run="mkdir -p results && env"
    while IFS= read -r v; do [ -n "$v" ] && run+=" $(printf %q "$v")"; done <<<"$vars"
    run+=" ./pi.py$(printf ' %q' "$@") 2>&1 | tee -a $log; exec bash"
    $SSH pi@"$IP" "tmux kill-session -t pi 2>/dev/null; tmux new-session -d -s pi -c ~/sl/agent bash -lc $(printf %q "$run")"
    for _ in $(seq 30); do
        dir=$($SSH pi@"$IP" 'for f in ~/sl/agent/results/*/pid; do [ -f "$f" ] && ps -p "$(cat "$f")" -o command= | grep -q pi.py && basename "${f%/pid}"; done' || true)
        [ -n "$dir" ] && break
        sleep 1
    done
    [ -n "$dir" ] || { echo "pi.py did not start; see ~/sl/agent/$log on the box" >&2; exit 1; }
    echo "started $dir, logging to ~/sl/agent/$log"
    echo "attach: ssh -t pi@$IP tmux attach -t pi    status: $0 status $IP    fetch: $0 fetch $IP"
    ;;
status)
    $SSH pi@"$IP" python3 - <<'PY'
import json, subprocess
from pathlib import Path
runs = sorted(Path.home().glob("sl/agent/results/*/run.json"))
if not runs:
    print("no runs")
for rec in runs:
    d = rec.parent
    pid = (d / "pid").read_text().strip() if (d / "pid").exists() else ""
    live = pid.isdigit() and "pi.py" in subprocess.run(["ps", "-p", pid, "-o", "command="], capture_output=True, text=True).stdout
    sessions = sorted(s for s in d.iterdir() if s.name.isdigit())
    last = sessions[-1] / "transcript.log" if sessions else None
    context = next((l for l in reversed(last.read_text(errors="replace").splitlines()) if l.startswith("[context")), "") if last and last.exists() else ""
    print(f"{'live' if live else 'stopped'}  {d.name}  {sum((s / 'answer.txt').exists() for s in sessions)}/{json.loads(rec.read_text())['n']} sessions done  {context}")
PY
    ;;
fetch)
    mkdir -p "agent/results/box-$IP"
    rsync -a -e "$SSH" pi@"$IP":sl/agent/results/ "agent/results/box-$IP/"
    echo "fetched into agent/results/box-$IP ($(du -sh "agent/results/box-$IP" | cut -f1))"
    ;;
esac
