#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
TAG=pi-harness
. agent/ssh.sh
. agent/do.sh

free() {
    (set -a; . "${PI_DEPLOY_ENV:-$HOME/.config/pi/deploy.env}"; set +a
     curl -s https://api.neuralwatt.com/v1/chat/completions -H "Authorization: Bearer $NEURALWATT_API_KEY" -H "Content-Type: application/json" \
         -d "{\"model\": \"$1\", \"messages\": [{\"role\": \"user\", \"content\": \"hi\"}], \"max_tokens\": 1, \"reasoning_effort\": \"$2\"}") |
        python3 -c 'import json, sys; sys.exit(json.load(sys.stdin)["cost"]["request_cost_usd"] != 0)'
}

ips=$(rows | awk '{print $1}')
for ip in $ips; do
    if agent/run.sh status "$ip" 2>/dev/null | grep -q '^live '; then echo "$ip has a live run; starting nothing"; exit 0; fi
done
models=
free deepseek-v4.1-flash-flex none && models+=,deepseek-v4.1-flash-flex || echo "no free energy for deepseek-v4.1-flash-flex"
free glm-5.3-flash-flex low && models+=,glm-5.3-flash-flex || echo "no free energy for glm-5.3-flash-flex"
[ -n "$models" ] || exit 0
ip=$(head -1 <<<"$ips")
echo "starting ${models#,} on ${ip:-a new droplet}"
exec agent/run.sh ${ip:+"$ip"} --models "${models#,}" tasks/false.txt
