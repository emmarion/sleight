SSH="ssh -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ControlMaster=auto -o ControlPath=$HOME/.ssh/pi-cm-%C -o ControlPersist=300"
connect() {
    for _ in $(seq 12); do
        $SSH -o ConnectTimeout=10 "$1" true 2>/dev/null && return
        sleep 5
    done
    $SSH "$1" true
}
