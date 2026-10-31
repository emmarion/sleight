#!/bin/sh
# usage: fourcolor/check.sh [final|many] [slc|ref] [extra compiler arguments...]
set -eu
cd "$(dirname "$0")/.."
goal=${1:-final}; [ $# -gt 0 ] && shift
comp=${1:-slc}; [ $# -gt 0 ] && shift
case $comp in
  slc) C=_build/release/slc ;;
  ref) C=_build/default/bin/main.exe ;;
  *) echo "unknown compiler: $comp" >&2; exit 2 ;;
esac
case $goal in
  final) mid=""; last=fcfinal ;;
  many) mid="paint fcmany"; last=fcmanyfinal ;;
  *) echo "unknown goal: $goal" >&2; exit 2 ;;
esac
F="std/macro.sl std/nat.sl std/list.sl fourcolor/ring.sl"
for x in defs orient base sweep geo plan map lists planemap walk frontier labels rot fan build readback $mid \
  parta reduce hypgraph hypperm hypermap hypplane reduce2 hypeuler hypderived hyprelabel hypwalkup hypgeom \
  hypjordan hyptree hypcount hypcubic cube reduce3 coloring induct inductfc cfmap colalias \
  hypsub unav/faces red/red cpmap red/color cfcolor red/ctree red/gtree red/grestrict red/crestrict red/kempe \
  cpcolor red/configs red/bridge red/init red/check red/gramrot red/cfred red/ccomp red/ccheck red/bcheck \
  cpcomp iealias realias ringtrace kempemap patch patch2 split geomring sew snip srcycle revsnip revsnip2 \
  revsnip3 cpgeom ringdec traceconv birkhoff birkfit birkhoff2 embed2 contract contract2 unav/realias; do
  F="$F fourcolor/$x.sl"
done
for x in part quiz hubcap present fit dbound hubcapc obsmap dscore dsum posz pwalk hubsound pwsound \
  conv cap unav data qfit rdart redc qwalk qembed qcert qtree qmirror unave; do
  F="$F fourcolor/unav/$x.sl"
done
for x in embed birkhoff3 minarity embed3 embed5 contract3 embed6 fullred trivred notembed evalid triad trivfive \
  red/chunks fcopen native embed4 red/pieces red/proof-c red/bproof unav/qztproof embed4proof fcproof $last; do
  F="$F fourcolor/$x.sl"
done
export OCAMLRUNPARAM="${OCAMLRUNPARAM:-o=400}"
exec $C $F --goal proved --inline 50 "$@"
