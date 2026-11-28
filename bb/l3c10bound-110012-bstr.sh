#!/bin/sh
# usage: bb/l3c10bound-110012-bstr.sh [extra slc arguments...]
set -eu
cd "$(dirname "$0")/.."
ulimit -s unlimited
F="std/list.sl std/immediate.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl std/macro.sl bb/skelet.sl bb/space.sl bb/sk17.sl bb/rle.sl bb/l3.sl bb/l3tok.sl bb/l3round.sl bb/l3jump.sl bb/l3phi.sl bb/l3dec.sl bb/l3life.sl bb/l3walk.sl bb/l3train.sl bb/l3c10.sl bb/l3c10-chain.sl bb/l3c10h.sl bb/l3c10-aend.sl bb/l3c10-desc.sl bb/l3c10-child.sl bb/l3c10-death.sl bb/l3c10-uniform.sl bb/l3c10-childh.sl bb/l3c10-local.sl bb/l3c10-local-tbl.sl bb/l3c10-child2.sl bb/l3c10-absorb2.sl bb/l3c10-blklaw.sl bb/l3c10-blklaw2.sl bb/l3c10-run.sl bb/l3c10-far.sl bb/l3c10-train.sl bb/l3c10-trlaw.sl bb/l3c10-chf.sl bb/l3c10-junc.sl bb/l3c10-far2.sl bb/l3c10-par.sl bb/l3c10-par37.sl bb/l3c10-par110.sl bb/l3c10-bstr.sl bb/l3c10bound-110012-bstr.sl"
exec _build/release/slc $F --goal proved "$@"
