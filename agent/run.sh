#!/bin/bash
set -eu
TAG=pi-harness
SIZE=${SIZE:-s-2vcpu-4gb}
usage() {
    cat >&2 <<EOF
usage: $0 [IP] [--models M,...] [--copies N] [--per-box K] [--size S] PI-ARGS...
           start N copies [1] of pi.py PI-ARGS (paths relative to agent/) per model, each in its own tmux
           session, passing on PI_* variables: on IP, after deploying HEAD there, or else on new $TAG
           droplets in the first of $REGIONS offering size $SIZE of K runs each [all of them]; M is provider:model, or a model
           whose provider is guessed: claude-* anthropic, gpt-* openai, else neuralwatt [\$PI_MODEL]
       $0 resume [-n N] RUN-DIR [IP]
           continue a fetched or local run: on IP if it still has the run, else on a new droplet that gets
           HEAD and a copy of RUN-DIR; -n sets a new session total
       $0 deploy IP
           deploy HEAD to IP; a live run's next session uses its code, prompt files, headers and compiler
       $0 set-n IP [RUN] N
           change a live run's session total, read before each session: a larger N continues it, a smaller
           one stops it after the current session; RUN defaults to the box's only live run
       $0 ls
           list the $TAG droplets and their runs
       $0 status IP
           list the runs on the box
       $0 tail [-t] IP [RUN]
           follow a live run's log, or with -t its current session's transcript; RUN defaults to the
           box's only live run
       $0 fetch IP
           copy the box's results into agent/results/box-NAME/; each session's sandbox is mirrored, so files the agent
           has since deleted or moved go, and nothing else local is removed
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
. agent/do.sh

box_dir() { local name; name=$(droplet "$1" | cut -d' ' -f2); echo "agent/results/box-${name:-$1}"; }

live() { connect pi@"$1" && $SSH pi@"$1" 'for f in ~/sl/agent/results/*/pid; do [ -f "$f" ] && ps -p "$(cat "$f")" -o command= | grep -q pi.py && basename "${f%/pid}"; done; true'; }

pick() {
    local runs
    runs=$(live "$1")
    if [ -n "${2:-}" ]; then run=$2; else
        [ "$(grep -c . <<<"$runs")" = 1 ] || { echo "$1 has $(grep -c . <<<"$runs") live runs; name one:" $runs >&2; exit 1; }
        run=$runs
    fi
    grep -qx "$run" <<<"$runs"
}

unfetched() { connect pi@"$1" && rsync -an --copy-unsafe-links --out-format=%n -e "$SSH" pi@"$1":sl/agent/results/ "$(box_dir "$1")/" | grep -v '/$' || true; }

slug() { echo "$1" | tr -c 'a-zA-Z0-9.\n-' -; }

guess() {
    case $1 in
    - | *:*) echo "$1" ;;
    claude-*) echo "anthropic:$1" ;;
    gpt-*) echo "openai:$1" ;;
    *) echo "neuralwatt:$1" ;;
    esac
}

task() {
    local t=
    while [ $# -gt 0 ]; do
        case $1 in
        -f | -k | -c | -n) shift 2 ;;
        --no-header) shift ;;
        *) t+=${t:++}$(basename "${1%.*}"); shift ;;
        esac
    done
    echo "$t"
}

fill() {
    local ip=$1 m
    shift
    agent/deploy.sh "$ip"
    for m; do
        if [ "$m" = - ]; then launch "$ip" "${args[@]}"; else PI_PROVIDER=${m%%:*} PI_MODEL=${m#*:} launch "$ip" "${args[@]}"; fi
    done
}

launch() {
    local ip=$1 stamp log run vars before dir=
    shift
    stamp=$($SSH pi@"$ip" date +%Y%m%d-%H%M%S-%3N) log=results/$stamp.log
    vars=$(env | grep -E '^PI_' | grep -vE '^PI_(SLC|DEPLOY_ENV|DO_ENV)=' || true)
    run="mkdir -p results && env"
    while IFS= read -r v; do [ -n "$v" ] && run+=" $(printf %q "$v")"; done <<<"$vars"
    run+=" ./pi.py$(printf ' %q' "$@") 2>&1 | tee -a $log; exec bash"
    before=$(live "$ip")
    $SSH pi@"$ip" "tmux new-session -d -s pi-$stamp -c ~/sl/agent bash -lc $(printf %q "$run")"
    for _ in $(seq 30); do
        dir=$(comm -13 <(sort <<<"$before") <(live "$ip" | sort) || true)
        [ -n "$dir" ] && break
        sleep 1
    done
    [ -n "$dir" ] || { echo "pi.py did not start; see ~/sl/agent/$log on the box" >&2; exit 1; }
    echo "started $dir on $ip, logging to ~/sl/agent/$log"
    echo "attach: ssh -t pi@$ip tmux attach -t pi-$stamp    status: $0 status $ip    fetch: $0 fetch $ip"
}

cmd=start
case "${1:-}" in resume | deploy | set-n | ls | status | tail | fetch | destroy | reap) cmd=$1; shift ;; esac
if [ $cmd = start ]; then
    ip= models=- copies=1 per_box= sized=
    [[ ${1:-} =~ ^[0-9]+(\.[0-9]+){3}$ ]] && { ip=$1; shift; }
    while :; do
        case "${1:-}" in
        --size) export SIZE=$2 sized=1; shift 2 ;;
        --models) models=$2; shift 2 ;;
        --copies) [[ $2 =~ ^[1-9][0-9]*$ ]] || usage; copies=$2; shift 2 ;;
        --per-box) [[ $2 =~ ^[1-9][0-9]*$ ]] || usage; per_box=$2; shift 2 ;;
        *) break ;;
        esac
    done
fi

case $cmd in
start)
    [ $# -ge 1 ] || usage
    args=("$@") runs=()
    for m in ${models//,/ }; do
        for _ in $(seq "$copies"); do runs+=("$(guess "$m")"); done
    done
    if [ -n "$ip" ]; then
        [ -z "$per_box$sized" ] || usage
        fill "$ip" "${runs[@]}"
    else
        k=${per_box:-${#runs[@]}} name=pi-$(slug "$(task "$@")")-$(date +%m%d-%H%M%S)
        n=$(((${#runs[@]} + k - 1) / k))
        for ((b = 0; b < n; b++)); do
            (create "$name$([ $n = 1 ] || echo -$((b + 1)))"; fill "$ip" "${runs[@]:b*k:k}") 2>&1 | sed "s/^/[box $((b + 1))] /" &
        done
        wait
    fi
    ;;
deploy)
    [ $# -eq 1 ] || usage
    agent/deploy.sh "$1"
    ;;
resume)
    n=
    [ "${1:-}" = -n ] && { n=$2; shift 2; }
    [ $# -ge 1 ] && [ $# -le 2 ] || usage
    dir=${1%/} run=$(basename "${1%/}")
    [ -f "$dir/run.json" ] || { echo "$dir has no run.json" >&2; exit 1; }
    if [ $# -eq 2 ]; then ip=$2; else create "pi-$(slug "$run")"; fi
    agent/deploy.sh "$ip"
    if $SSH pi@"$ip" test -e "sl/agent/results/$run"; then
        echo "$ip already has results/$run; resuming that copy"
    else
        $SSH pi@"$ip" mkdir -p sl/agent/results
        rsync -a --copy-unsafe-links --exclude pid -e "$SSH" "$dir/" pi@"$ip":sl/agent/results/"$run"/
        $SSH pi@"$ip" python3 - "$run" <<'PY'
import json, sys
from pathlib import Path
agent = Path.home() / "sl/agent"
f = agent / "results" / sys.argv[1] / "run.json"
rec = json.loads(f.read_text())
here = lambda p: str(agent / p.split("/agent/", 1)[1]) if "/agent/" in p else p
rec["prompts"] = [here(p) for p in rec["prompts"]]
if "flags" in rec:
    rec["flags"] = [(f, here(v) if f == "-f" else v) for f, v in rec["flags"]]
else:
    rec["seeds"] = [here(p) for p in rec["seeds"]]
rec["env"].pop("PI_SLC", None)
f.write_text(json.dumps(rec, indent=1) + "\n")
PY
    fi
    launch "$ip" -r "results/$run" ${n:+-n "$n"}
    ;;
ls)
    lock=$(mktemp -u)
    while read -r ip id name size price age <&3; do
        {
            block="$ip  $name  $size  $price  $age"
            if out=$(agent/run.sh status "$ip" 2>/dev/null); then block+=$'\n'$(sed 's/^/    /' <<<"$out"); else block+=$'\n    (unreachable)'; fi
            n=$(unfetched "$ip" 2>/dev/null | wc -l | tr -d ' ')
            [ "$n" = 0 ] || block+=$'\n'"    $n files not fetched"
            until mkdir "$lock" 2>/dev/null; do sleep 0.05; done
            printf '%s\n' "$block"
            rmdir "$lock"
        } &
    done 3< <(rows)
    wait
    ;;
set-n)
    [ $# -eq 2 ] || [ $# -eq 3 ] || usage
    ip=$1 n=${!#}
    [[ $n =~ ^[0-9]+$ ]] || usage
    pick "$ip" "$([ $# -eq 3 ] && echo "$2")" || { echo "$run is not live on $ip; continue it with $0 resume -n $n" >&2; exit 1; }
    $SSH pi@"$ip" python3 - "$run" "$n" <<'PY'
import json, os, sys
from pathlib import Path
d = Path.home() / "sl/agent/results" / sys.argv[1]
f, n = d / "run.json", int(sys.argv[2])
started = max((int(s.name) for s in d.iterdir() if s.name.isdigit()), default=1)
if n < started:
    print(f"clamped {n} to {started}: session {started} is already under way or done")
    n = started
rec = json.loads(f.read_text())
old, rec["n"] = rec["n"], n
tmp = f.with_name("run.json.tmp")
tmp.write_text(json.dumps(rec, indent=1) + "\n")
os.replace(tmp, f)
print(f"{d.name}: n {old} -> {n}, read before its next session")
PY
    ;;
status)
    [ $# -eq 1 ] || usage
    connect pi@"$1"
    $SSH pi@"$1" python3 - <<'PY'
import json, re, subprocess
from pathlib import Path
def spent(log):
    m = next((m for l in reversed(log.read_text(errors="replace").splitlines()) if (m := re.search(r", \$([\d.]+)(?:, ([\d,.]+) J)? spent", l))), None)
    return (float(m[1]), float((m[2] or "0").replace(",", ""))) if m else (0, 0)
def charged(f):
    return sum(t.get("charged_energy_kwh") or 0 for t in json.loads(f.read_text()).get("turns") or [])
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
    info = json.loads(rec.read_text())
    used = sessions[-1] / "session.json" if sessions else None
    env = json.loads(used.read_text())["env"] if used and used.exists() else info["env"]
    settings = " ".join(f"{k}={v}" for k, v in sorted(env.items()) if k not in ("PI_MODEL", "PI_PROVIDER"))
    done = f"{sum((s / 'answer.txt').exists() for s in sessions)}/{info['n']} done"
    cost, energy = map(sum, zip((0, 0), *map(spent, d.glob("*/transcript.log"))))
    total = f"${cost:.4f}, {energy:,.0f} J in all" if cost or energy else ""
    kwh = list(map(charged, d.glob("*/nw-session.json")))
    billed = f"{sum(kwh) * 1000:,.1f} Wh, ${sum(kwh) * 7:.4f} at $7/kWh, over {len(kwh)} session{'s' * (len(kwh) != 1)}" if kwh else ""
    ctx, _, session = context.removeprefix("[context: ").removesuffix("]").partition(", $")
    print(("live" if live else "stopped") + "  " + d.name)
    for label, value in (("sessions", done), ("spent", total), ("charged", billed), ("settings", settings), ("context", ctx), ("session", session and "$" + session)):
        if value:
            print(f"    {label:<9} {value}")
PY
    ;;
tail)
    t=
    [ "${1:-}" = -t ] && { t=1; shift; }
    [ $# -eq 1 ] || [ $# -eq 2 ] || usage
    pick "$1" "${2:-}" || { echo "$run is not live on $1" >&2; exit 1; }
    if [ -n "$t" ]; then f="\$(ls -d $run/[0-9][0-9] | tail -1)/transcript.log"; else f="\$(grep -l results/$run/ *.log | tail -1)"; fi
    exec $SSH -t pi@"$1" "cd sl/agent/results && tail -n 20 -F $f"
    ;;
fetch)
    [ $# -eq 1 ] || usage
    dir=$(box_dir "$1")
    mkdir -p "$dir"
    connect pi@"$1"
    rsync -a --copy-unsafe-links -e "$SSH" pi@"$1":sl/agent/results/ "$dir/"
    rsync -a --copy-unsafe-links --delete --include='/*/' --include='/*/[0-9][0-9]/' --include='/*/[0-9][0-9]/sandbox/***' --exclude='*' \
        -e "$SSH" pi@"$1":sl/agent/results/ "$dir/"
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
            agent/run.sh fetch "$ip" && agent/run.sh destroy --yes "$ip"
        fi
    done 3< <(rows)
    ;;
esac
