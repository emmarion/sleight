#!/bin/sh
cd "$(dirname "$0")/.." || exit 1
RUN=${SLEIGHT:-dune exec bin/main.exe --}
PROOF="std/nat.sl stlc/types.sl stlc/curry.sl"
LEMMAS="stlc/skip.sl stlc/ctx.sl stlc/subst.sl stlc/jm.sl stlc/reducts.sl stlc/steps.sl stlc/proof.sl"
$RUN $PROOF stlc/spec.sl $LEMMAS stlc/qed.sl --goal proved "$@" &&
$RUN $PROOF $LEMMAS stlc/curry-names.sl stlc/ispec.sl stlc/ibridge.sl stlc/iqed.sl --goal proved "$@"
