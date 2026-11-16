#!/bin/bash
R=$(cd "$(dirname "$0")/../../../../.." && pwd)
MAIN=${REF:-$R/_build/default/bin/main.exe}
SLC=${SLC:-$R/_build/release/slc}
here=$(cd "$(dirname "$0")" && pwd)
S4=$(dirname "$here")
tmp=$(mktemp -d "$here/tmp.XXXXXX")
for fmt in "$@"; do
  printf "$fmt" > "$tmp/case.sl"
  r=$("$MAIN" --no-shape-note "$here/showargs.sl" "$tmp/case.sl" 2>&1 | grep -v 'lopsided' | sed "s|$tmp/||g" | head -4)
  s=$("$SLC" --interpret --no-shape-note "$here/showargs.sl" "$tmp/case.sl" 2>&1 | grep -v 'lopsided' | sed "s|$tmp/||g" | head -4)
  m=$("$MAIN" "$S4/syntax.sl" "$S4/spec.sl" "$S4/read.sl" "$S4/show.sl" "$S4/cli.sl" < "$tmp/case.sl" 2>&1 | head -4)
  printf 'text      : %s\n  main.exe  : %s\n  slc       : %s\n  prototype : %s\n' "$fmt" "$r" "$s" "$m"
done
rm -rf "$tmp"
