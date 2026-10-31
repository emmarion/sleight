# The structure of the four colour proof

Written by Claude sessions working without the owner. It describes the
proof as the files appear to have it; where it and the code differ, the
code is what the compilers check. README.md says what is proved and how
to run it.

## Architecture

The theorem is `defs.sl`'s `FourColor`: every straight-line drawing with
natural coordinates whose edges are pairwise `Compatible` has a `Proper`
colouring of its points with colours below 4. The proof splits at plane
maps:

- **Part A** (`Drawing` to `PlaneMap`): a sweep over the points turns a
  drawing into a `PlaneMap` of `map.sl`, a map built an edge at a time
  (`PMIsolated`, `PMPendant`, `PMChord`), and reads a proper colouring of
  the drawing back from a `Colored` colouring of the map. SWEEP.md gives
  the idea. `parta.sl`'s `part-a` takes the two halves as functions, and
  `reduce.sl` closes the geometric half with `plan.sl`'s `drawing-plan`.
  Part A is this repository's own; it does not follow the Coq proof,
  whose geometry works in the real plane.
- **Part B** (plane maps are four-colourable): Gonthier and Werner's Coq
  proof (NOTICE.md), restated in Sleight. A `PlaneMap` is a hypermap of
  genus 0 that is bridgeless (`hypplane.sl`'s `plane-hypermap`), so
  `reduce2.sl` needs a four-colouring of every planar bridgeless hypermap;
  `cubegoal.sl`'s cube construction reduces that to plain cubic maps
  (`reduce3.sl`), and `inductfc.sl` gets those from an `Analysis` by
  induction on the number of darts. `embed.sl`'s `embed-analysis` builds
  the `Analysis` from unavoidability, reducibility and the Birkhoff
  checks.

## Minimality as data

Coq's proof argues from a minimal counterexample. Here the induction
(`induct.sl`'s `four-color-induct`) is one function, `col-all`, and a
function minted while it runs cannot be called from it (DESIGN.md §17,
WORKAROUNDS.md 1–2), so the argument is turned round:

- `Pbpp d e n f`: a hypermap on d darts that is planar, bridgeless, plain
  and precubic. `NoColoring` is a certificate that the search of
  `coloring.sl` (`color-dec`) found no four-colouring.
- `Reduces B d e n f`: a list `ms` of maps (`Mp`), each `Pbpp` and on
  fewer darts (`Smaller`), with a `ColorFrom B`: a witness of a type the
  reduction chooses and a glue function at a level that predates the
  bound B, turning four-colourings of `ms` (`MpCols`) into one of the map.
- `Analysis`: a function, at a level of its own, giving every `Pbpp` map
  with a `NoColoring` a `Reduces B` for a bound B it fixes.

`col-all` colours a list of maps below a bound: each map by the search
or, when the search fails, by the glue of its reduction applied to the
colourings of its smaller maps. Every lemma that would conclude "the
counterexample is not minimal" instead returns a `Reduces`
(`split-reduces`, `birkhoff-reduces`, `cubic-reduces`, `not-embed`, ...),
and `reduces-lift` raises its bound.

`embed-analysis` (`embed.sl`) refutes the `NoColoring` of a map with no
dart, splits a disconnected one (`split.sl`), and otherwise takes, in
turn:

1. `BirkGeo` (`minarity.sl`'s `birk-geo-of`, from `BirkhoffChecks`): the
   map is plain cubic with every face above four darts (`Geo`), or it
   reduces;
2. `UnavE cfs`: some configuration of cfs has its kernel preembedded in
   the map or its mirror (`CfEmbed`);
3. `AllRedC X css`: that configuration is C-reducible (`CRed X`);
4. `NotEmbed X cfs` (`notembed.sl`'s `not-embed`, from `BirkhoffChecks`
   and `CfCerts cfs`): such a preembedded C-reducible configuration makes
   the map reduce; `reduces-mirror` carries a reduction of the mirror back.

`fcopen.sl`'s `four-color-open` puts this together: `FourColor` from the
four computed facts `UnavE cfs`, `AllRedC CRX css`, `BirkhoffChecks` and
`CfCerts cfs`, with no other hypothesis.

## C-reducibility and levels

`CRed X` (`red/cfred.sl`) states C-reducibility with a co-closure
function at a level X, which glue at a fixed level must be able to call.
So the `red/` files mint fixed top-level levels (`KCB` in `red/bridge.sl`,
`COB` and `KHL` in `red/cfred.sl`, `CGL` in `red/ccomp.sl`, `CRX` in
`red/ccheck.sl`), and a caller at a level K builds `CoLv` evidence from
levels it mints at the top level after them, then mints K, with X before
K. `notembed.sl` is the caller that follows this recipe.

## The four computed checks

Each check is a certified function: it returns its fact with erased
evidence, or fails. Each is queued with `native.sl`'s macros and all of
them run in one `native-compute` (DESIGN.md §72, WORKAROUNDS.md 7):

| fact | proof file | jobs |
|---|---|---|
| `AllRedC CRX css`: each of the 633 configurations is C-reducible | `red/proof-c.sl` | one per piece of `red/pieces.sl` (96) |
| `BirkhoffChecks`: Birkhoff2 to Birkhoff5 of `birkhoff.v` | `red/bproof.sl` | 4 |
| `UnavE cfs`: unavoidability, through the presentations of hub arities 5 to 11 and the cap checks | `unav/qztproof.sl` | one per region of the walks (21) and one for the caps |
| `CfCerts cfs`: per-configuration embedding certificates | `embed4proof.sl` | one per chunk of `red/chunks.sl` (32) |

`(native-jobs name ev job ...)` queues thunks with a pattern each and
evidence `ev`; `(native-each name xs (x t r) T e pat step nil)` queues one
job per element of a `Settled` list and folds their evidence;
`(native-then stmt ...)` queues statements; `(native-run)` runs every
queued thunk in one `native-compute`, matches each result against its
pattern, binds each name to its evidence and runs the queued statements.
The queue is the last of `native-queue-0`, `native-queue-1`, ... in
scope. `fcproof.sl` calls `native-run` and binds `four-color-proof`.

The configurations reach the jobs as strings (`red/configs.sl`'s
`config-srcs`) that each job decodes and checks; `DecList`, `DecAll`
and `Flatten` tie what is decoded to the lists `css`, `pcs` and `cfs`
the goal types name, and `cfs-run` re-decodes `cfs` inside a job with an
`Eq` to it (WORKAROUNDS.md 8). The cut into pieces affects only how the
jobs balance; any sizes give the same theorem.

## Load order

The unit is these files in this order (`check.sh`), written without
`fourcolor/` and `.sl`. `fcmany.sl`'s unit adds `paint fcmany` after
`readback` and ends with `fcmanyfinal` in place of `fcfinal`.

**Prelude.** `std/macro.sl std/nat.sl std/list.sl`, then
- `ring`: a reflective semiring decision procedure over `Nat`
  (`Expr`, `Norm`, `RingEq`), numeral lemmas, list relations.

**Statement and part A.**
- `defs`: `Point`, `Edge`, `Left`, `Compatible`, `Drawing`, `Proper`,
  `FourColor`.
- `orient`: the shoelace sign behind `Left` and its basic lemmas.
- `base`: `Or`, `In`, `NotIn`, `Distinct`.
- `sweep`: `SweepPlan`, between the geometric and combinatorial halves.
- `geo`, `plan`: the sweep's geometry; `drawing-plan`.
- `map`: `PlaneMap`, `FaceReach`, `Insert`, `Colored`.
- `lists`, `planemap`, `walk`, `frontier`, `labels`, `rot`: list and
  `PlaneMap` lemmas, face walks avoiding corners, the frontier of corner
  groups, node labels and representatives, rotations.
- `fan`, `build`: one step of the sweep; a whole sweep to a `PlaneMap`.
- `readback`: `plan-map`, `plan-paint`.
- `parta`: `part-a`. `reduce`: `FourColor` from colouring every `PlaneMap`.

**Hypermaps.**
- `hypgraph`, `hypperm`: bond graphs, classes; permutations, orbits.
- `hypermap`: `Hypermap`, `Genus`, `Bridgeless`, `FourColoring`.
- `hypplane`: `plane-hypermap`. `reduce2`: `hyp-reduction`.
- `hypeuler`, `hypderived`, `hyprelabel`, `hypwalkup`: Euler's equation
  and the genus, dual and mirror, renaming darts, Walkup transforms.
- `hypgeom`: definitions of `geometry.v` (`Moebius`, `Connected`,
  `Precubic`, `AllOrder`, `SCycle`, `Fband`, `Kernel`, ...).
- `hypjordan`, `hyptree`, `hypwalkeq`, `hypcount`, `hypcubic`:
  `planar-moebius`, Euler for trees, the equality case of Walkup,
  `orbit-sum`, cubic Euler.
- `cube`, `cubegoal`: the cube construction; `cube-reduction`.
- `reduce3`: `cubic-reduction`.
- `coloring`: the colouring search (`search-ring`, `NoExt`,
  `noext-sound`); colourings of the dual and mirror.
- `induct`, `inductfc`: the induction; `four-color-from`.

**Configurations and reducibility.**
- `cfmap`, `colalias`, `hypsub`: configuration maps from their programs;
  aliases; sub-lists of darts and their classes.
- `unav/faces`: face iterates and arities.
- `red/red`: `Config`, colours, program steps, trees.
- `cpmap`: `Cpmap`, `PointedMap`, `cpmap-c`.
- `red/color`, `cfcolor`: colour traces, `CpCol`.
- `red/ctree`, `red/gtree`, `red/grestrict`, `red/crestrict`,
  `red/kempe`: the check's trees, their restrictions, the Kempe closure
  (`kempe-tree-c`) on unique trees (WORKAROUNDS.md 11).
- `cpcolor`: ring traces of a configuration's colourings (`cpcolor-c`).
- `red/configs`: `config-srcs` (generated), its decoder, `cut-at`.
- `red/bridge`: co-closure on complete traces (`KCC`, `kcc-coclosure`).
- `red/init`, `red/check`: the initial trees; `kempe-tree-chk`.
- `red/gramrot`: gram_rot of `kempe.v`.
- `red/cfred`: `CRed`, from a Kempe half and a contract half.
- `red/ccomp`: the contract half (`contract-ok`, `dfs-c`).
- `red/ccheck`: `CfContract`, `valid-c`, `red-c`, `AllRedC`.
- `red/bcheck`: `birkhoff-check-c`, `birkhoff-check-sound`,
  `BirkhoffChecks`.
- `cpcomp`: the completeness half of ctree_mem_cpcolor.

**Map surgery.**
- `iealias`, `realias`: aliases.
- `ringtrace`, `kempemap`: ring traces; `kempe.v` (`kempe-map`).
- `patch`, `patch2`: `Patch`; `gcomp-split`, `bridgeless-patch`.
- `split`: `split-reduces`.
- `geomring`: simple_cface, `quasicubic-euler`.
- `sew`, `snip`, `srcycle`: `sew-exists`; `Ring`, `DiskN`, `DiskF`,
  `snip-exists`; srcycles are rings.
- `revsnip`, `revsnip2`, `revsnip3`: reversed rings, `NonTrivial`,
  `cotrace`, chord rings, `ring-disk-closed`, `ring-disk-chord`.
- `cpgeom`: `cpmap-geom`. `ringdec`: `decide-ring-trace`.
- `traceconv`: `cfcolor.sl`'s traces as `ringtrace.sl`'s.

**Birkhoff and contraction.**
- `birkhoff`, `birkfit`, `birkhoff2`: Birkhoff_valid (`birkhoff-maps`)
  and Birkhoff's theorem (`birkhoff-reduces`).
- `embed2`: colourings along dart maps (`embed-color`, `rem-kempe`).
- `contract`, `contract2`: `Contraction` (contract_coloring).
- `unav/realias`: an alias.

**Unavoidability** (all in `unav/`).
- `part`, `quiz`, `hubcap`, `present`: parts and ranges, quizzes,
  hubcaps, `Script` and `script-from`.
- `fit`, `dbound`, `hubcapc`, `obsmap`, `dscore`, `dsum`, `posz`: part
  operations, dbound and hubcap checks, a dart of positive dscore.
- `pwalk`, `hubsound`, `pwsound`, `conv`, `cap`: the presentation walk
  (`check2-c`) and its soundness; the caps of larger hubs.
- `unav`: `Checked`. `data`: rules and scripts (generated).
- `qfit`, `rdart`, `redc`: a certified redpart (`redp-c`, `red-sound`).
- `qwalk`, `qembed`, `qcert`, `qtree`, `qmirror`: `quiz-preembedding`,
  its certificates (`cfqz-c`), the quiz tree (`qzt-hit`), `geo-mirror`.
- `unave`: `UnavE`, `CfEmbed`, `MapOrMirror`.

**Embedding and assembly.**
- `embed`: `BirkGeo`, `NotEmbed`, `ConcatL`, `embed-analysis`.
- `birkhoff3`, `minarity`: `cubic-reduces`; min_arity, `birk-geo-of`.
- `embed3`, `embed5`, `embed6`: embedding a preembedded kernel (`EEnv`,
  `HEmb`, `embed-main`, `FullRedR`, `patch-open`).
- `contract3`: the bridgeless part of contract_coloring.
- `fullred`, `trivred`: embed_full (`full-red-of`, `triv-red-of`).
- `notembed`: `not-embed`, `CfCerts`, `EmbedValid`, `TriadFive`.
- `evalid`, `triad`, `trivfive`: `embed-valid`, `triad-five`,
  `triv-five`.
- `red/chunks`: 32 chunks of 20 configurations, the last of 13 (`css`).
- `fcopen`: `cfs`, `cfs-run`, `four-color-open`.

**Computed proofs and goal.**
- `native`: the queueing macros.
- `embed4`: per-configuration certificates (`CfGc`, `cfcerts-of`).
- `red/pieces`: 96 pieces (`pcs`), `allredc-pieces`.
- `red/proof-c`, `red/bproof`, `unav/qztproof`, `embed4proof`: the
  four checks, queued.
- `fcproof`: `native-run`, `four-color-proof`. `fcfinal`: the goal.
- `paint`, `fcmany`, `fcmanyfinal`: `FourColorM`, the theorem as a
  program: `paint-go` searches for a colouring and the erased
  `FourColor` refutes its failure (`four-color-m`).

`spec.sl` sets the goal `FourColor` alone and is in no chain.

## Standalone check units

Each computed check also has a unit of its own, a goal file of three
lines run with `--goal proved` (and, as in `check.sh`, `--inline 200`),
its files named as in the load order:

- `red/goal-c.sl` (`AllRedC CRX css`): `std/macro.sl native
  std/nat.sl std/list.sl ring base map lists planemap walk frontier labels
  hypgraph hypperm hypermap hypplane hypeuler hypderived hyprelabel
  hypwalkup hypgeom cfmap red/red cpmap red/color cfcolor red/ctree
  red/gtree red/grestrict red/crestrict red/kempe cpcolor red/configs
  red/bridge red/init red/check red/gramrot red/cfred red/ccomp
  red/ccheck red/chunks red/pieces red/proof-c red/goal-c`.
- `red/bgoal.sl` (`BirkhoffChecks`): the same up to `red/ccheck`, then
  `red/bcheck red/bproof red/bgoal`.
- `unav/qztgoal.sl` (`UnavE cfs`): `std/macro.sl native std/nat.sl
  std/list.sl ring defs orient base sweep geo plan map lists planemap walk
  frontier labels rot fan build readback parta reduce hypgraph hypperm
  hypermap hypplane reduce2 hypeuler hypderived hyprelabel hypwalkup
  hypgeom hypjordan hyptree hypwalkeq hypcount hypcubic cfmap colalias
  unav/faces red/red cpmap red/color cfcolor red/configs unav/realias`,
  then `unav/` `part quiz hubcap present fit dbound hubcapc obsmap dscore
  dsum posz pwalk hubsound pwsound conv cap unav data qfit rdart redc
  qwalk qembed qcert qtree qmirror unave qztcfs qztproof qztgoal`.
  `unav/qztcfs.sl` binds `cfs` and `cfs-run` by decoding `config-srcs`,
  as `fcopen.sl` does in the full unit.
- `embed4goal.sl` (`CfCerts cfs`): the full unit up to `embed4`, then
  `embed4proof embed4goal`.

`paint-run.sl` runs `paint.sl`'s search on a drawing of K4: part A's
files up to `readback`, then `paint paint-run`.

## Generated data

- `red/gen.py configurations.v` prints the `config-srcs` binding that
  `red/configs.sl` holds: each of the 633 configurations of Coq's
  `configurations.v` (`Definition cfN := Config ...`) as one string of
  bytes holding its symmetry flag, its contract and its program.
- `unav/gen.py <coq dir> unav/data.sl` reads `discharge.v` (the
  discharging rules, as `base-drules`) and `present5.v` to `present11.v`
  (the presentation scripts) and writes `unav/data.sl`. Each script is
  spelt as a skeleton string with each largest subtree of 100 to 800
  leaves cut out as its own string (`script-src`), which
  `present.sl`'s `script-from` puts back (`script-by`).

The data is checked, not trusted: the theorem does not mention it, and
wrong data appears able only to make a check fail.

## Trust

The theorem `fcfinal.sl` discharges is `defs.sl`'s `FourColor`, the
owner's statement. Its proof appears to rest on:

- the compilers' type checking and the elaborator's evaluator;
- the compiled `native-compute` runs (DESIGN.md §29, §72) and the OCaml
  toolchain they use;
- nothing else: no axiom of its own and no hypothesis.

The intermediate statements are meant to follow Coq's (C_reducible,
valid_contract, the preembedding and kernel, the mirror, nontrivial
rings, chords, even and ring traces, ...). That they match has been
checked only by reading. A mismatch would bear on the attribution in
NOTICE.md and on this guide, not on what `FourColor` states.

## Open

- The match of the intermediate statements with Coq's, above, is
  checked only by reading; `red/ccheck.sl`'s `CfContract` is written for
  this repository's dart numbering and not checked against Coq's
  cfcontract.
- That `Compatible` means what README.md reads it as (two edges meet at
  most at a shared endpoint) is checked only by reading.
- The timings in README.md are single runs on a shared machine.
