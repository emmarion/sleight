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

create() {
    local keys
    keys=$(dctl compute ssh-key list --format ID,FingerPrint --no-header | while read -r id fp; do
        for f in ~/.ssh/*.pub; do [ "MD5:$fp" = "$(ssh-keygen -E md5 -lf "$f" | awk '{print $2}')" ] && echo "$id"; done
    done | paste -sd, -)
    [ -n "$keys" ] || { echo "none of ~/.ssh/*.pub is among the account's SSH keys" >&2; exit 1; }
    ip=$(dctl compute droplet create "$1" --region nyc3 --size "$SIZE" --image ubuntu-24-04-x64 --ssh-keys "$keys" \
        --tag-name $TAG --wait --format PublicIPv4 --no-header)
    echo "created $1 at $ip; waiting for ssh"
    ssh-keygen -R "$ip" >/dev/null 2>&1 || true
    connect root@"$ip"
}
