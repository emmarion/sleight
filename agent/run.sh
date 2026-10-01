#!/bin/bash
set -eu
TAG=pi-harness
SIZE=${SIZE:-s-2vcpu-4gb}
usage() {
    cat >&2 <<EOF
usage: $0 IP PI-ARGS...
           deploy HEAD to IP, then start pi.py PI-ARGS (paths relative to agent/) in tmux session pi,
           passing on PI_* variables
       $0 new [--size S] PI-ARGS...
           create a $TAG droplet in nyc3 (size $SIZE), then deploy and start
       $0 sweep --models M,... [--size S] PI-ARGS...
           one new droplet per model; M is provider:model, or a model whose provider is guessed:
           claude-* anthropic, gpt-* openai, else neuralwatt
       $0 ls
           list the $TAG droplets and their runs
       $0 status IP
           list the runs on the box
       $0 fetch IP
           copy the box's results into agent/results/box-NAME/
       $0 destroy [--force] [--yes] IP
           destroy a $TAG droplet; --force even with a live or unfetched run
       $0 reap
           fetch, then destroy, every $TAG droplet with no live run
The DigitalOcean token is read from \$PI_DO_ENV [~/.config/pi/do.env] and never leaves this machine.
EOF
    exit 2
}
cd "$(dirname "$0")/.."
. agent/ssh.sh

dctl() { (set -a; . "${PI_DO_ENV:-$HOME/.config/pi/do.env}"; set +a; exec doctl "$@"); }

rows() {
    dctl compute droplet list --tag-name $TAG --output json | python3 -c '
import datetime, json, sys
for d in json.load(sys.stdin) or []:
    ip = next((n["ip_address"] for n in d["networks"]["v4"] if n["type"] == "public"), "-")
    age = datetime.datetime.now(datetime.timezone.utc) - datetime.datetime.fromisoformat(d["created_at"].replace("Z", "+00:00"))
    price = d["size"]["price_hourly"]
    print(ip, d["id"], d["name"], d["size_slug"], f"${price:.3f}/h", f"up {age.total_seconds() / 3600:.1f}h")'
}

droplet() { rows 2>/dev/null | awk -v ip="$1" '$1 == ip {print $2, $3}'; }

box_dir() { local name; name=$(droplet "$1" | cut -d' ' -f2); echo "agent/results/box-${name:-$1}"; }

live() { connect pi@"$1" && $SSH pi@"$1" 'for f in ~/sl/agent/results/*/pid; do [ -f "$f" ] && ps -p "$(cat "$f")" -o command= | grep -q pi.py && basename "${f%/pid}"; done; true'; }

unfetched() { connect pi@"$1" && rsync -an --out-format=%n -e "$SSH" pi@"$1":sl/agent/results/ "$(box_dir "$1")/" | grep -v '/$' || true; }

start() {
    local ip=$1 log run vars dir=
    shift
    agent/deploy.sh "$ip"
    log=results/$($SSH pi@"$ip" date +%Y%m%d-%H%M%S).log
    vars=$(env | grep -E '^PI_' | grep -vE '^PI_(SLC|DEPLOY_ENV|DO_ENV)=' || true)
    run="mkdir -p results && env"
    while IFS= read -r v; do [ -n "$v" ] && run+=" $(printf %q "$v")"; done <<<"$vars"
    run+=" ./pi.py$(printf ' %q' "$@") 2>&1 | tee -a $log; exec bash"
    $SSH pi@"$ip" "tmux kill-session -t pi 2>/dev/null; tmux new-session -d -s pi -c ~/sl/agent bash -lc $(printf %q "$run")"
    for _ in $(seq 30); do
        dir=$(live "$ip" || true)
        [ -n "$dir" ] && break
        sleep 1
    done
    [ -n "$dir" ] || { echo "pi.py did not start; see ~/sl/agent/$log on the box" >&2; exit 1; }
    echo "started $dir on $ip, logging to ~/sl/agent/$log"
    echo "attach: ssh -t pi@$ip tmux attach -t pi    status: $0 status $ip    fetch: $0 fetch $ip"
}

cmd=start
case "${1:-}" in new | sweep | ls | status | fetch | destroy | reap) cmd=$1; shift ;; esac
if [ "$cmd" = new ] || [ "$cmd" = sweep ]; then
    models=
    while :; do
        case "${1:-}" in
        --size) export SIZE=$2; shift 2 ;;
        --models) [ $cmd = sweep ] || usage; models=$2; shift 2 ;;
        *) break ;;
        esac
    done
fi

case $cmd in
start)
    [ $# -ge 2 ] || usage
    start "$@"
    ;;
new)
    [ $# -ge 1 ] || usage
    keys=$(dctl compute ssh-key list --format ID,FingerPrint --no-header | while read -r id fp; do
        for f in ~/.ssh/*.pub; do [ "MD5:$fp" = "$(ssh-keygen -E md5 -lf "$f" | awk '{print $2}')" ] && echo "$id"; done
    done | paste -sd, -)
    [ -n "$keys" ] || { echo "none of ~/.ssh/*.pub is among the account's SSH keys" >&2; exit 1; }
    name=pi-$(echo "${PI_MODEL:-default}" | tr -c 'a-zA-Z0-9.\n-' -)-$(date +%m%d-%H%M%S)
    ip=$(dctl compute droplet create "$name" --region nyc3 --size "$SIZE" --image ubuntu-24-04-x64 --ssh-keys "$keys" \
        --tag-name $TAG --wait --format PublicIPv4 --no-header)
    echo "created $name at $ip; waiting for ssh"
    ssh-keygen -R "$ip" >/dev/null 2>&1 || true
    connect root@"$ip"
    start "$ip" "$@"
    ;;
sweep)
    [ -n "$models" ] && [ $# -ge 1 ] || usage
    for m in ${models//,/ }; do
        case $m in
        *:*) p=${m%%:*}; m=${m#*:} ;;
        claude-*) p=anthropic ;;
        gpt-*) p=openai ;;
        *) p=neuralwatt ;;
        esac
        PI_PROVIDER=$p PI_MODEL=$m "$0" new "$@" 2>&1 | sed "s/^/[$m] /" &
    done
    wait
    ;;
ls)
    while read -r ip id name size price age <&3; do
        echo "$ip  $name  $size  $price  $age"
        if ! "$0" status "$ip" 2>/dev/null | sed 's/^/    /'; then echo "    (unreachable)"; fi
        n=$(unfetched "$ip" 2>/dev/null | wc -l | tr -d ' ')
        [ "$n" = 0 ] || echo "    $n files not fetched"
    done 3< <(rows)
    ;;
status)
    [ $# -eq 1 ] || usage
    connect pi@"$1"
    $SSH pi@"$1" python3 - <<'PY'
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
    [ $# -eq 1 ] || usage
    dir=$(box_dir "$1")
    mkdir -p "$dir"
    connect pi@"$1"
    rsync -a -e "$SSH" pi@"$1":sl/agent/results/ "$dir/"
    echo "fetched into $dir ($(du -sh "$dir" | cut -f1))"
    ;;
destroy)
    force=0 yes=0
    while :; do
        case "${1:-}" in
        --force) force=1; shift ;;
        --yes) yes=1; shift ;;
        *) break ;;
        esac
    done
    [ $# -eq 1 ] || usage
    read -r id name <<<"$(droplet "$1")" || true
    [ -n "${id:-}" ] || { echo "$1 is not a $TAG droplet; refusing" >&2; exit 1; }
    if [ $force = 0 ]; then
        l=$(live "$1") || { echo "cannot reach pi@$1 to check for a live run; pass --force" >&2; exit 1; }
        [ -z "$l" ] || { echo "a run is live on $name; pass --force" >&2; exit 1; }
        [ -z "$(unfetched "$1")" ] || { echo "$name has unfetched results; run $0 fetch $1, or pass --force" >&2; exit 1; }
    fi
    if [ $yes = 0 ]; then
        read -r -p "destroy $name ($id, $1)? [y/N] " answer </dev/tty
        [ "$answer" = y ] || exit 1
    fi
    dctl compute droplet delete "$id" --force
    ssh-keygen -R "$1" >/dev/null 2>&1 || true
    echo "destroyed $name"
    ;;
reap)
    while read -r ip id name rest <&3; do
        if ! l=$(live "$ip" 2>/dev/null); then
            echo "skipping $name ($ip): unreachable"
        elif [ -n "$l" ]; then
            echo "skipping $name ($ip): $l is live"
        else
            "$0" fetch "$ip" && "$0" destroy --yes "$ip"
        fi
    done 3< <(rows)
    ;;
esac
