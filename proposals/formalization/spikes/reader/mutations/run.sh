#!/bin/bash
R=$(cd "$(dirname "$0")/../../../../.." && pwd)
MAIN=${REF:-$R/_build/default/bin/main.exe}
here=$(cd "$(dirname "$0")" && pwd)
S4=$(dirname "$here")
tmp=$(mktemp -d)
python3 - "$S4" "$tmp" <<'PY'
import sys
S4,tmp=sys.argv[1],sys.argv[2]
syn=open(S4+'/syntax.sl').read()
read=open(S4+'/read.sl').read()
def mutate(src,old,new,out):
    assert old in src
    open(tmp+'/'+out,'w').write(src.replace(old,new))
mutate(syn,"(erased (Apart (Char) CharLt c #\\newline) a) (erased (Comment rest after) p)","(erased (Char) a) (erased (Comment rest after) p)","m1-syntax.sl")
mutate(syn,"(many WordStop : (erased (Char) c) (erased (Delim) d) (erased (String) rest) (erased (Class delims c (KDelim d)) k)","(many WordStop : (erased (Char) c) (erased (Delim) d) (erased (String) rest) (erased (Kind) k)","m2-syntax.sl")
mutate(syn,"  (many ItemsDollar :","  (many ItemsDollarEnd : (erased (List (Tok)) ts) (erased (List (Form)) inner) (erased (Items ts inner (AtEnd)) p)\n     -> (Items (Cons (Tok) (TDollar) ts) (Cons (Form) (FList inner) (Nil (Form))) (AtEnd)))\n  (many ItemsDollar :","m3-syntax.sl")
mutate(syn,"(Cons _ (MkEntry #\\space (DSpace)) $","(Cons _ (MkEntry #\\x0c (DSpace)) $ Cons _ (MkEntry #\\x0b (DSpace)) $ Cons _ (MkEntry #\\space (DSpace)) $","m5-syntax.sl")
mutate(read,"((AtClose after) (ParsedOk _ (Cons _ (FList inner) (Nil _)) end (ItemsDollar ts after inner p)))","((AtClose after) (ParsedOk _ (Cons _ (FList inner) (Nil _)) (AtEnd) (ItemsDollar ts after inner p)))","m4-read.sl")
PY
show() { sed "s|$tmp/||g; s|$S4/||g" | head -3; }
echo "M0 unmutated: syntax.sl proof.sl"
"$MAIN" "$S4/syntax.sl" "$S4/proof.sl" 2>&1 | show; echo "  exit ${PIPESTATUS[0]}"
echo "M1 a comment may skip a newline: m1-syntax.sl proof.sl"
"$MAIN" "$tmp/m1-syntax.sl" "$S4/proof.sl" 2>&1 | show
echo "M2 a word may stop at any character: m2-syntax.sl proof.sl"
"$MAIN" "$tmp/m2-syntax.sl" "$S4/proof.sl" 2>&1 | show
echo "M3 a \$ form may run to the end of the text: m3-syntax.sl proof.sl"
"$MAIN" "$tmp/m3-syntax.sl" "$S4/proof.sl" 2>&1 | show
echo "M4 the reader lets \$ consume the ): syntax.sl m4-read.sl"
"$MAIN" "$S4/syntax.sl" "$tmp/m4-read.sl" 2>&1 | show
echo "M5 form feed and vertical tab added to the table (not a weakening): m5-syntax.sl spec.sl read.sl proof.sl qed.sl --goal proved"
"$MAIN" "$tmp/m5-syntax.sl" "$S4/spec.sl" "$S4/read.sl" "$S4/proof.sl" "$S4/qed.sl" --goal proved 2>&1 | show
printf '(a\fb)' | "$MAIN" "$tmp/m5-syntax.sl" "$S4/read.sl" "$S4/show.sl" "$S4/cli.sl"
printf '(a\fb)' | "$MAIN" "$S4/syntax.sl" "$S4/read.sl" "$S4/show.sl" "$S4/cli.sl" | cat -v
rm -rf "$tmp"
