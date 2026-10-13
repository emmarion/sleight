#!/bin/sh
cd "$(dirname "$0")"
files="heapsort_cert.dats cert_entry.dats"
lib=/usr/lib/ats2-postiats-0.4.2
echo "== forbidden constructs in $files"
grep -nE 'praxi|\$UN|extern[[:space:]]+prfun|extern[[:space:]]+prfn|solver_assert|patsolve|PERMUTE|SORT\(|LTB|LTEB|ISORD' $files || echo "(none)"
echo "== extern declarations: the FFI boundary of the benchmark harness (heapsort itself uses none)"
grep -n 'extern' $files
echo "== proof functions and where they are defined (each has its body at that site)"
grep -nE '^(prfun|prfn|propdef|dataprop|dataview)' $files
echo "== identifiers used that the prelude or libats declares as praxi/prfun/prfn"
grep -rhoE '^[[:space:]]*(praxi|prfun|prfn)[[:space:]]+[A-Za-z_][A-Za-z0-9_]*' $lib/prelude $lib/libats |
  awk '{print $2}' | sort -u > /tmp/libproofs.txt
grep -rhE '^(praxi|prfun|prfn)$' -A1 $lib/prelude $lib/libats | grep -oE "^[A-Za-z_][A-Za-z0-9_]*" | grep -vxE "praxi|prfun|prfn" | sort -u >> /tmp/libproofs.txt
sed 's/(\*.*\*)//' $files | grep -oE '[A-Za-z_][A-Za-z0-9_]*' | sort -u > /tmp/used.txt
own=$(grep -hoE '^(prfun|prfn)[[:space:]]+[A-Za-z_][A-Za-z0-9_]*' $files | awk '{print $2}' | sort -u)
hits=$(sort -u /tmp/libproofs.txt | comm -12 - /tmp/used.txt | grep -vxF "$own")
[ -z "$hits" ] && echo "(none)" || echo "$hits"
echo "== type-check with ilist_prf.sats replaced by a copy of only ilist, LENGTH, NTH, UPDATE"
tmp=$(mktemp -d)
cat > $tmp/ilist_min.sats <<'S'
datasort ilist = ilist_nil of () | ilist_cons of (int, ilist)
stadef ilist_sing (x:int) = ilist_cons (x, ilist_nil)
dataprop LENGTH (ilist, int) =
  | LENGTHnil(ilist_nil, 0) of ()
  | {x:int}{xs:ilist}{n:nat} LENGTHcons(ilist_cons (x, xs), n+1) of LENGTH (xs, n)
dataprop NTH (x0:int, ilist, int) =
  | {xs:ilist} NTHbas (x0, ilist_cons (x0, xs), 0)
  | {x1:int}{xs:ilist}{n:nat} NTHind (x0, ilist_cons (x1, xs), n+1) of NTH (x0, xs, n)
dataprop UPDATE (yi: int, ilist, int, ilist) =
  | {x0:int}{xs:ilist} UPDATEbas (yi, ilist_cons (x0, xs), 0, ilist_cons (yi, xs)) of ()
  | {x:int}{xs:ilist}{i:nat}{ys:ilist}
    UPDATEind (yi, ilist_cons (x, xs), i+1, ilist_cons (x, ys)) of UPDATE (yi, xs, i, ys)
S
sed "s|staload \"libats/SATS/ilist_prf.sats\"|staload \"$tmp/ilist_min.sats\"|" heapsort_cert.dats > $tmp/heapsort_cert.dats
sed "s|#include \"heapsort_cert.dats\"|#include \"$tmp/heapsort_cert.dats\"|" cert_entry.dats > $tmp/cert_entry.dats
patsopt -tc -d $tmp/cert_entry.dats > $tmp/log 2>&1 && ! grep -q error $tmp/log && echo "ok" || cat $tmp/log
rm -rf $tmp
