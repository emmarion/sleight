#!/bin/bash
set -eu
TAG=rea
SIZE=${SIZE:-s-4vcpu-16gb-amd}
SWAP=${SWAP:-16G}
CACHE=~/.cache/sleight
usage() {
    cat >&2 <<EOF
usage: $0 create [--slc FILE|REV]
           create a $TAG droplet in the first of $REGIONS offering size $SIZE (swap $SWAP) with Java 21, binutils, OCaml, Node 24, Claude Code, Ghidra
           and REA (github.com/morluto/rea, registered with Claude Code), and a user slc with passwordless sudo
           whose ~/slc/slc, never run, is FILE or slc built at REV [HEAD] (cached in ${CACHE/#$HOME/~}); Claude Code
           there trusts ~/slc; from a terminal, the script ends by signing it in to your Claude subscription and
           starting a Remote Control session in ~/slc, in tmux session claude
       $0 build [REV [OUT]]
           build slc at REV [HEAD] on a temporary droplet tagged $TAG-build, copy the x86-64 Linux binary to OUT
           [./slc-x86_64-linux-SHORTHASH], and destroy the droplet
       $0 ls
           list the $TAG droplets
       $0 destroy [--yes] IP
           destroy a $TAG droplet
The DigitalOcean token is read from \$PI_DO_ENV [~/.config/pi/do.env] and never leaves this machine.
EOF
    exit 2
}
here=$PWD
cd "$(dirname "$0")/.."
. agent/ssh.sh
. agent/do.sh
APT='cloud-init status --wait >/dev/null 2>&1 || true
while fuser /var/lib/dpkg/lock-frontend /var/lib/apt/lists/lock >/dev/null 2>&1; do sleep 3; done
export DEBIAN_FRONTEND=noninteractive NEEDRESTART_SUSPEND=1
apt-get update -qq'
abs() { case $1 in /*) echo "$1" ;; *) echo "$here/$1" ;; esac; }

case "${1:-}" in
create)
    [ $# -eq 1 ] || { [ $# -eq 3 ] && [ "$2" = --slc ]; } || usage
    slc=${3:-HEAD}
    if [ -f "$(abs "$slc")" ]; then slc=$(abs "$slc"); else
        rev=$(git rev-parse --verify "$slc^{commit}")
        slc=$CACHE/slc-x86_64-linux-$rev
        [ -f "$slc" ] || { mkdir -p "$CACHE"; agent/rea.sh build "$rev" "$slc"; }
    fi
    name=$TAG-$(rows | awk -v t="$TAG-" 'index($3, t) == 1 && substr($3, length(t) + 1) + 0 > m {m = substr($3, length(t) + 1) + 0} END {print m + 1}')
    create "$name"
    { echo "SWAP=$SWAP"; echo "$APT"; cat <<'EOF'; } | $SSH root@"$ip" sh -eu
fallocate -l "$SWAP" /swapfile
chmod 600 /swapfile
mkswap /swapfile >/dev/null
swapon /swapfile
echo '/swapfile none swap sw 0 0' >> /etc/fstab
apt-get install -y -qq curl git unzip openjdk-21-jdk binutils ocaml ocaml-findlib libzarith-ocaml-dev >/dev/null
curl -fsSL https://deb.nodesource.com/setup_24.x -o /tmp/nodesource.sh
bash /tmp/nodesource.sh >/dev/null 2>&1
rm /tmp/nodesource.sh
apt-get install -y -qq nodejs >/dev/null
useradd -m -s /bin/bash slc
install -d -o slc -g slc -m 700 /home/slc/.ssh
install -o slc -g slc -m 600 /root/.ssh/authorized_keys /home/slc/.ssh/
echo 'slc ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/90-slc
chmod 440 /etc/sudoers.d/90-slc
visudo -cf /etc/sudoers.d/90-slc >/dev/null
install -d -o slc -g slc -m 755 /home/slc/slc
EOF
    ${SSH/ssh/scp} -q "$slc" slc@"$ip":slc/slc
    $SSH slc@"$ip" bash -eu <<'EOF'
chmod 755 ~/slc/slc
curl -fsSL https://claude.ai/install.sh | bash >/dev/null
mkdir -p ~/.claude
cat > ~/.claude/CLAUDE.md <<'MD'
# This machine

You are on a private, disposable VPS that exists only for this work and is destroyed afterwards. You have passwordless sudo. Install whatever you need (system packages, language packages, or tools built from source) without asking first.
MD
python3 -c 'import json, os; f = os.path.expanduser("~/.claude/settings.json"); d = json.load(open(f)) if os.path.exists(f) else {}; d.setdefault("permissions", {})["defaultMode"] = "bypassPermissions"; d["skipDangerousModePermissionPrompt"] = True; json.dump(d, open(f, "w"), indent=2)'
mkdir -p ~/tools && cd ~/tools
curl -fsSLO "$(curl -fsSL https://api.github.com/repos/NationalSecurityAgency/ghidra/releases/tags/Ghidra_12.1.4_build | grep -o 'https://[^"]*PUBLIC[^"]*\.zip' | head -1)"
unzip -q ghidra_*.zip && rm ghidra_*.zip
ln -s ~/tools/ghidra_*_PUBLIC ~/tools/ghidra
sudo npm install --global --silent rea-agents@6.7.0 >/dev/null
export GHIDRA_INSTALL_DIR=$(readlink -f ~/tools/ghidra)
echo "export GHIDRA_INSTALL_DIR=$GHIDRA_INSTALL_DIR" >> ~/.profile
rea setup --yes --client claude_code --json | python3 -c 'import json, sys; d = json.load(sys.stdin); sys.exit(d["status"] != "ready" or not d["doctor"]["healthy"])'
python3 -c 'import json, os; f = os.path.expanduser("~/.claude.json"); d = json.load(open(f)); d.update(hasCompletedOnboarding=True, theme="dark"); d.setdefault("projects", {}).setdefault(os.path.expanduser("~/slc"), {})["hasTrustDialogAccepted"] = True; json.dump(d, open(f, "w"), indent=2)'
echo "java: $(java -version 2>&1 | head -1); node: $(node --version); claude: $(~/.local/bin/claude --version); ghidra: $(basename "$GHIDRA_INSTALL_DIR"); rea: $(rea --version)"
~/.local/bin/claude mcp list 2>/dev/null | grep '^rea:'
echo "slc: $(sha256sum ~/slc/slc)"
EOF
    if [ -t 0 ]; then
        $SSH -t slc@"$ip" '~/.local/bin/claude auth login'
        $SSH slc@"$ip" bash -ls <<<"tmux new-session -d -s claude -x 200 -y 50 -c ~/slc '~/.local/bin/claude --remote-control $name'"
        for _ in $(seq 20); do
            url=$($SSH slc@"$ip" tmux capture-pane -p -t claude | grep -o 'https://claude\.ai/code/session_[A-Za-z0-9_]*' || true)
            [ -n "$url" ] && break
            sleep 2
        done
        echo "remote control: ${url:-no session link yet; see ssh -t slc@$ip tmux attach -t claude}"
    else
        echo "sign Claude Code in to your subscription with: ssh -t slc@$ip '~/.local/bin/claude auth login'"
    fi
    echo "ready: ssh slc@$ip"
    ;;
build)
    [ $# -le 3 ] || usage
    rev=$(git rev-parse --verify "${2:-HEAD}^{commit}")
    out=$(abs "${3:-slc-x86_64-linux-${rev:0:7}}")
    TAG=$TAG-build
    create "$TAG-${rev:0:7}"
    trap 'dctl compute droplet delete --force "$(droplet "$ip" | cut -d" " -f1)" && ssh-keygen -R "$ip" >/dev/null 2>&1; echo "destroyed the build droplet"' EXIT
    git archive "$rev" | $SSH root@"$ip" 'mkdir sl && tar -x -C sl'
    { echo "$APT"; cat <<'EOF'; } | $SSH root@"$ip" sh -eu
apt-get install -y -qq ocaml-nox ocaml-findlib libzarith-ocaml-dev ocaml-dune >/dev/null
sh sl/self/release.sh >/dev/null
EOF
    ${SSH/ssh/scp} -q root@"$ip":sl/_build/release/slc "$out"
    echo "built $out from ${rev:0:7}: $(shasum -a 256 "$out" | cut -d' ' -f1)"
    ;;
ls)
    rows
    ;;
destroy)
    yes=0
    [ "${2:-}" = --yes ] && { yes=1; shift; }
    [ $# -eq 2 ] || usage
    read -r id name <<<"$(droplet "$2")" || true
    [ -n "${id:-}" ] || { echo "$2 is not a $TAG droplet; refusing" >&2; exit 1; }
    if [ $yes = 0 ]; then
        read -r -p "destroy $name ($id, $2)? [y/N] " answer </dev/tty
        [ "$answer" = y ] || exit 1
    fi
    dctl compute droplet delete "$id" --force
    ssh-keygen -R "$2" >/dev/null 2>&1 || true
    echo "destroyed $name"
    ;;
*) usage ;;
esac
