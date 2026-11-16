#!/bin/bash
R=$(cd "$(dirname "$0")/../../../../.." && pwd)
MAIN=${REF:-$R/_build/default/bin/main.exe}
SLC=${SLC:-$R/_build/release/slc}
here=$(cd "$(dirname "$0")" && pwd)
S4=$(dirname "$here")
tmp=$(mktemp -d)
mine() { printf '%s' "$1" | "$MAIN" "$S4/syntax.sl" "$S4/spec.sl" "$S4/read.sl" "$S4/show.sl" "$S4/cli.sl" 2>&1; }
accepted() {
  body=$(printf "$1")
  text="(show-args $body)"
  printf '%s' "$text" > "$tmp/case.sl"
  m=$(mine "$text")
  r=$("$MAIN" --no-shape-note "$here/showargs.sl" "$tmp/case.sl" 2>/dev/null)
  s=$("$SLC" --interpret --no-shape-note "$here/showargs.sl" "$tmp/case.sl" 2>/dev/null)
  r2="(show-args${r:+ }$(printf '%s' "$r" | sed 's/^"//; s/"$//'))"; [ "$r" = '""' ] && r2="(show-args)"
  s2="(show-args${s:+ }$(printf '%s' "$s" | sed 's/^"//; s/"$//'))"; [ "$s" = '""' ] && s2="(show-args)"
  verdict=AGREE; [ "$m" = "$r2" ] && [ "$m" = "$s2" ] || verdict=DIFFER
  printf '%s\n  text      : %q\n  prototype : %s\n  main.exe  : %s\n  slc       : %s\n' "$verdict" "$text" "$m" "$r2" "$s2"
}
rejected() {
  text=$(printf "$1")
  printf '%s' "$text" > "$tmp/case.sl"
  m=$(mine "$text")
  r=$("$MAIN" --no-shape-note "$tmp/case.sl" 2>&1 | grep -o 'error: .*' | head -1)
  s=$("$SLC" --interpret --no-shape-note "$tmp/case.sl" 2>&1 | grep -o 'error: .*' | head -1)
  verdict=AGREE; [ "$m" = "$r" ] && [ "$m" = "$s" ] || verdict=DIFFER
  printf '%s\n  text      : %q\n  prototype : %s\n  main.exe  : %s\n  slc       : %s\n' "$verdict" "$text" "$m" "$r" "$s"
}
accepted ''
accepted 'a'
accepted '(a b) c'
accepted 'a $ b $ c'
accepted 'f (g $ h i) j'
accepted 'a $'
accepted '$ $ a'
accepted 'foo$bar $$ a$ $b'
accepted 'a ; one ) (\n b'
accepted 'a;b\nc'
accepted 'a\t(b)\r\n'
accepted 'a $ b ; $ c\n $ d'
accepted 'x $ (y $ z) w'
rejected '(a b'
rejected '((a) (b'
rejected '(a $ (b'
rejected 'a) b'
rejected '(a)) (b'
rejected '$ a) b'
rejected '$ a'
rejected '(a $ b'
rejected '(a) $ b ; )'
rm -rf "$tmp"
