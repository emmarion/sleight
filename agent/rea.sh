#!/bin/bash
set -eu
TAG=rea
SIZE=${SIZE:-s-2vcpu-8gb-amd}
usage() {
    cat >&2 <<EOF
usage: $0 --slc FILE
           create a $TAG droplet in nyc3 (size $SIZE) with Java 21, binutils, OCaml, Node 24, Claude Code and
           Ghidra, and a user slc with passwordless sudo whose ~/slc/slc is a copy of FILE, which is never run
       $0 ls
           list the $TAG droplets
       $0 destroy [--yes] IP
           destroy a $TAG droplet
The DigitalOcean token is read from \$PI_DO_ENV [~/.config/pi/do.env] and never leaves this machine.
EOF
    exit 2
}
cd "$(dirname "$0")/.."
. agent/ssh.sh
. agent/do.sh

case "${1:-}" in
--slc)
    [ $# -eq 2 ] && [ -f "$2" ] || usage
    create "$TAG-$(rows | awk -v t="$TAG-" 'index($3, t) == 1 && substr($3, length(t) + 1) + 0 > m {m = substr($3, length(t) + 1) + 0} END {print m + 1}')"
    $SSH root@"$ip" sh -eu <<'EOF'
cloud-init status --wait >/dev/null 2>&1 || true
while fuser /var/lib/dpkg/lock-frontend /var/lib/apt/lists/lock >/dev/null 2>&1; do sleep 3; done
export DEBIAN_FRONTEND=noninteractive NEEDRESTART_SUSPEND=1
apt-get update -qq
apt-get install -y -qq curl git unzip openjdk-21-jdk binutils ocaml >/dev/null
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
    ${SSH/ssh/scp} -q "$2" slc@"$ip":slc/slc
    $SSH slc@"$ip" bash -eu <<'EOF'
chmod 755 ~/slc/slc
curl -fsSL https://claude.ai/install.sh | bash >/dev/null
mkdir -p ~/tools && cd ~/tools
curl -fsSLO "$(curl -fsSL https://api.github.com/repos/NationalSecurityAgency/ghidra/releases/latest | grep -o 'https://[^"]*PUBLIC[^"]*\.zip' | head -1)"
unzip -q ghidra_*.zip && rm ghidra_*.zip
ln -s ~/tools/ghidra_*_PUBLIC ~/tools/ghidra
echo "java: $(java -version 2>&1 | head -1); node: $(node --version); claude: $(~/.local/bin/claude --version); ghidra: $(basename "$(readlink ~/tools/ghidra)")"
echo "slc: $(sha256sum ~/slc/slc)"
EOF
    echo "ready: ssh slc@$ip"
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
