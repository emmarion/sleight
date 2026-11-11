#!/bin/sh
# usage: higman/check.sh [slc|ref] [k] [extra compiler arguments...]
set -eu
cd "$(dirname "$0")/.."
comp=${1:-slc}; [ $# -gt 0 ] && shift
case $comp in
  slc) C=_build/release/slc ;;
  ref) C=_build/default/bin/main.exe ;;
  *) echo "unknown compiler: $comp" >&2; exit 2 ;;
esac
case ${1:-} in
  ''|-*)
    F="std/nat.sl std/list.sl"
    for x in spec lexrun box measure forest dickson words higman; do F="$F higman/$x.sl"; done ;;
  *)
    k=$1; shift
    [ -f "higman/k$k.sl" ] || { echo "no higman/k$k.sl" >&2; exit 2; }
    F="std/nat.sl std/list.sl std/macro.sl"
    for x in kspec lexrun measure dm sre kforest kgen k$k ksearch; do F="$F higman/$x.sl"; done ;;
esac
exec $C $F --goal proved "$@"
