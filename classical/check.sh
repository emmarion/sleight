#!/bin/sh
cd "$(dirname "$0")/.." || exit 1
RUN=${SLEIGHT:-dune exec bin/main.exe --}
status=0
for f in classical/pass/*.sl; do
  if $RUN classical/defs.sl "$f" >/dev/null 2>&1; then :; else
    echo "FAIL: $f does not check"; status=1
  fi
done
tab=$(printf '\t')
while IFS="$tab" read -r name msg; do
  out=$($RUN classical/defs.sl "classical/fail/$name" 2>&1)
  if [ $? -eq 0 ]; then
    echo "FAIL: classical/fail/$name checks"; status=1
  elif ! printf '%s' "$out" | grep -qF -- "$msg"; then
    echo "FAIL: classical/fail/$name stops elsewhere"; status=1
  fi
done < classical/fail/expected.txt
[ $status -eq 0 ] && echo "classical: PASS"
exit $status
