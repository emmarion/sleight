# Third-party notices and credits for fourcolor/

Written by a Claude session at the owner's request; it is not legal
advice, and what the licenses require should be checked by the owner.

The statement in `defs.sl` and `spec.sl` is the owner's. The proof
around it is written in Sleight for this repository, but much of part B
(PLAN.md) is based on the Coq proof of the four colour theorem by
Georges Gonthier and Benjamin Werner, and some of its data is taken from
it. That proof is distributed under the CeCILL-B license, whose
Article 5.3.4 asks that a modified version say it is based on the
original and reproduce its intellectual property notice. This file is
meant to do that.

## Upstream project

- **The Four Color Theorem** in Coq, <https://github.com/math-comp/fourcolor>
  (authors: Georges Gonthier, initial, with Benjamin Werner; maintained
  in Coq-community by Yves Bertot). The copy this work followed is
  commit `c1d6b1cd5288bea4b067aac13cdde3c18dffe018`. Its source files
  carry the notice:

  > (c) Copyright 2006-2018 Microsoft Corporation and Inria.
  > Distributed under the terms of CeCILL-B.

  The license text is reproduced in [LICENSE-CeCILL-B.txt](LICENSE-CeCILL-B.txt).

The configurations, discharging rules and presentations in that proof
come in turn from the proof of N. Robertson, D. P. Sanders, P. Seymour
and R. Thomas, "The four-colour theorem", J. Combin. Theory Ser. B 70
(1997), 2–44.

## What is based on it

- Data, generated from the Coq files by scripts in this directory:
  `red/configs.sl` from `configurations.v` (by `red/gen.py`), and
  `unav/data.sl` from `discharge.v` and `present5.v` to `present11.v`
  (by `unav/gen.py`).
- Ports of its algorithms, function by function: `red/red.sl` (the
  reducibility check of `cfmap.v`, `cfcolor.v`, `cfcontract.v`,
  `ctree.v`, `gtree.v`, the restrict and init files, `kempetree.v` and
  `cfreducible.v`), and `unav/part.sl`, `quiz.sl`, `redpart.sl`,
  `hubcap.sl` and `present.sl` (the checks of `part.v`, `quiz.v`,
  `cfquiz.v`, `redpart.v`, `hubcap.v`, `discharge.v` and `present.v`).
- Definitions and proofs that follow the Coq development's statements,
  and often its proofs, in Sleight: the `hyp*.sl` files (`hypermap.v`,
  `geometry.v`, `walkup.v`, `jordan.v`), `cube.sl`, `coloring.sl`,
  `ringtrace.sl`, `ringdec.sl`, `kempemap.sl`, `patch.sl`, `snip.sl`,
  `revsnip.sl`, `revsnip2.sl`, `revsnip3.sl`, `hypsub.sl`, `geomring.sl`, `srcycle.sl` and `birkhoff.sl`
  (`cube.v`, `coloring.v`, `kempe.v`, `patch.v`, `snip.v`, `revsnip.v`,
  `geometry.v`, `birkhoff.v`), `cfmap.sl`, `cpmap.sl`, `cpgeom.sl`, `cfcolor.sl`, `cpcolor.sl`,
  `cpcomp.sl` and the certified files in `red/`
  (`color.v`, `chromogram.v`, `kempe.v`, `ctree.v`, `gtree.v`,
  `cfmap.v`, `cfcolor.v`, `cfcontract.v`, `kempetree.v`, `cfreducible.v`,
  `birkhoff.v`), and the
  certified files in `unav/` (`part.v`, `discharge.v`, `hubcap.v`,
  and for `qfit.sl`, `rdart.sl`, `redc.sl`, `qwalk.sl`, `qembed.sl`,
  `qcert.sl`, `qtree.sl`, `qmirror.sl`, `unave.sl` and `qztgoal.sl`, `quiz.v`,
  `cfquiz.v`, `quiztree.v`, `coloring.v`, `redpart.v` and
  `unavoidability.v`), and `embed.sl` (`present.v`, `coloring.v`, and
  the statements of `birkhoff.v` and `embed.v` that it takes as
  hypotheses), `induct.sl` and `inductgoal.sl` (the induction of
  the Coq proof's four_color_hypermap, and `coloring.v`'s
  minimal_counter_example, restated with minimality as data), `split.sl`
  (`patch.v`, `coloring.v`), `birkfit.sl` and `birkhoff2.sl`
  (`birkhoff.v`) and `embed2.sl` (`embed.v`).
  Where a Sleight file follows a Coq file, its comments or the commit
  that added it usually name the Coq file; this list is reconstructed
  from those and may be incomplete.

Part A (the reduction from straight-line drawings to plane maps:
`map.sl`, `sweep.sl`, `geo.sl`, `plan.sl`, `frontier.sl`, `fan.sl`,
`rot.sl`, `build.sl`, `readback.sl`, `parta.sl` and the `reduce*.sl`
files, with `ring.sl` and `orient.sl`) is this repository's own and is
not recorded as following the Coq proof, whose geometric part works with
the real plane instead.

## Citing

The Coq proof's authors point to these publications:

- G. Gonthier, "Formal Proof—The Four-Color Theorem", Notices of the AMS
  55(11), 2008, <https://www.ams.org/notices/200811/tx081101382p.pdf>.
- G. Gonthier, "A computer-checked proof of the Four Color Theorem",
  <https://inria.hal.science/hal-04034866/document>.
