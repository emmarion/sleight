#!/bin/sh
set -eu
FORCE=0
[ "${1:-}" = --force ] && { FORCE=1; shift; }
[ $# -eq 1 ] || { echo "usage: $0 [--force] IP   (deploys HEAD as user pi; --force even during a live pi.py run; keys: KEY=value lines in \$PI_DEPLOY_ENV [~/.config/pi/deploy.env], mode 0600)" >&2; exit 2; }
IP=$1
KEYS=${PI_DEPLOY_ENV:-$HOME/.config/pi/deploy.env}
cd "$(dirname "$0")/.."
[ -f "$KEYS" ] || { echo "no key file at $KEYS" >&2; exit 1; }
[ "$(stat -f %Lp "$KEYS" 2>/dev/null || stat -c %a "$KEYS")" = 600 ] || { echo "$KEYS must have mode 0600" >&2; exit 1; }
git diff --quiet HEAD || echo "warning: uncommitted changes are not deployed, only HEAD ($(git rev-parse --short HEAD))" >&2
. agent/ssh.sh
connect root@"$IP"

$SSH root@"$IP" "FORCE=$FORCE sh -eu" <<'EOF'
for f in /home/pi/sl/agent/results/*/pid; do
  if [ "$FORCE" = 0 ] && [ -f "$f" ] && ps -p "$(cat "$f")" -o command= 2>/dev/null | grep -q pi.py; then
    echo "a pi.py run is live in ${f%/pid}; stop it first, or pass --force" >&2
    exit 1
  fi
done
cloud-init status --wait >/dev/null 2>&1 || true
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq
apt-get install -y -qq git tmux rsync ocaml-nox ocaml-findlib libzarith-ocaml-dev ocaml-dune >/dev/null
id pi >/dev/null 2>&1 || useradd -m -s /bin/bash pi
loginctl enable-linger pi
install -d -o pi -g pi -m 700 /home/pi/.ssh
install -o pi -g pi -m 600 /root/.ssh/authorized_keys /home/pi/.ssh/
EOF
connect pi@"$IP"

$SSH pi@"$IP" 'umask 077; cat > ~/.pi.env' < "$KEYS"
git bundle create - HEAD 2>/dev/null | $SSH pi@"$IP" 'cat > ~/sl.bundle'

$SSH pi@"$IP" sh -eu <<'EOF'
grep -q pi.env ~/.profile || echo 'set -a; . ~/.pi.env; set +a' >> ~/.profile
[ -d ~/sl/.git ] || git init -q ~/sl
cd ~/sl
git fetch -q ~/sl.bundle HEAD
git checkout -q --detach FETCH_HEAD
rm ~/sl.bundle
if [ -x _build/release/slc ] && [ -f _build/release/slc.commit ] && git diff --quiet "$(cat _build/release/slc.commit)" HEAD -- self bin lib dune-project 2>/dev/null; then
  echo "slc is up to date (built at $(cut -c1-7 _build/release/slc.commit))"
else
  sh self/release.sh
  git rev-parse HEAD > _build/release/slc.commit
fi
python3 - <<'PY'
import os, sys, tempfile
from pathlib import Path
sys.path.insert(0, "agent")
import pi
pi.SANDBOX_ROOT = pi.RUN_DIR = Path(tempfile.mkdtemp())
pi.ROOT_FD = os.open(pi.SANDBOX_ROOT, os.O_RDONLY | os.O_DIRECTORY)
pi.write_bytes("a.sl", Path("tests/ackermann.sl").read_bytes())
assert "run: exit 0\n--- stdout ---\n9" in pi.sl("a.sl"), "sl smoke test failed"
why, _ = pi._proc([sys.executable, "-c", f"x = bytearray({pi.MEM_MB + 512} << 20); x[::4096] = b'x' * len(x[::4096])"], ".", 60, env={})
assert why, "the memory limit did not stop a program"
print(f"smoke test ok; over the {pi.MEM_MB} MB limit, a program {why}")
PY
echo "deployed $(git rev-parse --short HEAD); run with: ssh pi@<ip>, tmux, cd ~/sl/agent, ./pi.py ..."
EOF
