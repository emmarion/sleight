# Quasi-tactics in the four-colour proof: a census

Written by Claude sessions working without the owner. A survey of the hand-written lemmas in `fourcolor/`. The question was which of them really should be
produced by one generic tactic, how they sort into buckets, and how many lines they take. Everything here
is a reading by Claude sessions, not compiled fact, except where a compile check is cited. The proposed
tactics, library types and language changes are proposals for the owner; none is a decision.

## Contents

1. [Headline](#1-headline)
2. [Method and caveats](#2-method-and-caveats)
3. [What a quasi-tactic is here](#3-what-a-quasi-tactic-is-here)
4. [E1: derive from a relation's definition](#4-e1-derive-from-a-relations-definition)
5. [E2: structural rebuild](#5-e2-structural-rebuild)
6. [E3: decision procedures](#6-e3-decision-procedures)
7. [E4: hint search](#7-e4-hint-search)
8. [E5: reflection, soundness and bespoke checkers](#8-e5-reflection-soundness-and-bespoke-checkers)
9. [Not tactics: ergonomics, residue, duplicates](#9-not-tactics-ergonomics-residue-duplicates)
10. [Language and library alternatives (owner questions)](#10-language-and-library-alternatives-owner-questions)
11. [How the engines depend on each other](#11-how-the-engines-depend-on-each-other)
12. [Where it is concentrated](#12-where-it-is-concentrated)
13. [Suggested prototype order](#13-suggested-prototype-order)
14. [Open questions](#14-open-questions)
15. [Data files](#15-data-files)

## 1. Headline

The unit is a `def-fns` form, called a "lemma" below. Lines are physical source lines of the form. "Body"
excludes the signature (the header up to its closing parenthesis). Percentages are of the **46,645
lemma lines**, which leave out 3,427 lines of plain program code. For scale, the directory's 149 `.sl`
files hold 64,823 lines, of which 50,072 are inside the 4,396 `def-fns` forms.

| engine | what it would generate | lemmas | lines | % of lemma lines | body lines | H lines |
|---|---|---|---|---|---|---|
| **E1** derive from a relation | uniqueness, existence (erased and runtime), inversion, decidability, negation | 771 | 5,974 | 12.8% | 4,759 | 3,369 |
| **E2** structural rebuild | list-builder laws, transport/convert, Forall elimination, path kits, frames | 1,170 | 8,137 | 17.4% | 5,510 | 3,154 |
| **E3** decision procedures | finite `decide`, linear arithmetic, positional numerals/bits | 455 | 3,774 | 8.1% | 3,053 | 1,697 |
| **E4** hint search (`eauto`-like) | backward chaining, witness closing, small case splits | 268 | 1,567 | 3.4% | 963 | 798 |
| **E5** reflection | soundness folds, bespoke checkers | 88 | 1,439 | 3.1% | 1,222 | 105 |
| *subtotal E1–E3* | | *2,396* | *17,885* | *38.3%* | *13,322* | *8,220* |
| *subtotal E1–E5* | | *2,752* | *20,891* | *44.8%* | *15,507* | *9,123* |
| language ergonomics | record field adapters (named fields would remove them) | 223 | 1,316 | 2.8% | 827 | – |
| reassigned, not subcategorised | moved between groups in pass 2 (mostly glue/MAP) | 226 | 1,455 | 3.1% | 1,038 | – |
| residue | rotations, level factories, duplicates, small library | 79 | 770 | 1.7% | 596 | – |
| domain reasoning | hypermaps, Kempe chains, reducibility, geometry | 954 | 22,213 | 47.6% | 18,681 | – |
| *program code (excluded from %)* | searches, native jobs, `r4-run` | 162 | 3,427 | – | 3,221 | – |

How to read the bounds:

- **E1–E3 is the core claim: about 2,400 lemmas, 17,900 lines, 38% of lemma lines (28% of the
  directory).** Each lemma there is an instance of a schema that a classifier judged expressible as one
  generator parameterised by `def-adts` definitions plus a table of lemma names.
- **H lines (8,220 for E1–E3) are the floor.** These are the lemmas the classifier rated "the
  sketched tactic emits this with no per-lemma guidance". M lines need light guidance (which hint, which
  refuter); L lines have the generic skeleton but a non-generic step.
- **If the tactic takes the signature as input** (as `std/tactics.sl`'s `lt-lemma` does, §3), what it saves
  is the body: 13,300 lines for E1–E3. A derive-style tactic that also writes signatures saves the full lines.

The share of domain reasoning (48%) is higher than the first pass's 37%. Second-pass classifiers read
every form in detail and moved about 280 lemmas (4,600 lines) whose skeleton is generic but whose step is
real hypermap or Kempe reasoning into it. The tactic share barely moved (37% to 38%), because pass 2 also
pulled tactic-shaped lemmas out of the first pass's "glue" and "list library" buckets.

## 2. Method and caveats

1. **Extraction.** A script split every `.sl` file under `fourcolor/` into top-level forms by paren depth
   and kept the 4,396 `def-fns` forms, with name, file, line span and signature length.
2. **Pass 1.** 8 subagents, one per ~6,300-line chunk of whole files, read every form and gave each one
   of ~18 seed buckets, a confidence (H/M/L), the relation it is about, and a
   note. They invented ~20 extra buckets, which were merged by hand into the seed set.
3. **Pass 2.** 7 subagents, one per tactic group, re-read every form of their group and split it into
   subcategories, each meant to be one tactic schema or one library item. They re-rated confidence
   against their own tactic sketch, and flagged misbucketed rows. Groups were then regrouped into the
   five engines E1–E5 by hand; `quasi-tactics-census.tsv` records each lemma's engine and subcategory.
4. **Spot checks.** About 15 randomly chosen H-rated forms were read by the main session and matched
   their labels.

What to distrust:

- **Labels are judgement, not compilation.** No tactic was built. "H" means a reader believed the
  sketched generator would emit the form, not that one did.
- **Reading depth varied.** Some pass-1 agents read long forms truncated or classified from signatures
  and call lists. Pass 2 read everything, but used scripts for first guesses before hand correction.
- **The relation counts** come from a free-text "family" field and are approximate.
- **Schemas are written informally.** Arrows mean the lemma's telescope; `∃` means multiple returned
  values via `values`.
- **`def-adts` lines are not counted** (6,984 lines). Several alternatives in §10 would also delete
  type definitions, so their payoff is larger than the lemma lines show.
- **One claim was compiled** (§10.1). Everything else said about what Sleight can or cannot express is a
  reading of the code and DESIGN.md and may be wrong.

## 3. What a quasi-tactic is here

The repository already has one. `std/tactics.sl` defines `lt-lemma`, a macro that takes a lemma's raw
signature, reads its `Lt`/`NatLe`/`Ne`/`Add`/`Double` hypotheses, finds a chain from hypotheses to the goal,
and emits the `def-fns` with a proof body. `heapsort/flat/arith.sl` uses it:

```
(lt-lemma (erased le-lt-lt : (erased (Nat) a b c) (erased (NatLe a b) p) (erased (Lt b c) q) -> (erased (Lt a c) r)))
```

The four-colour proof does not load `std/tactics.sl`. `check.sh` loads only `std/macro.sl`, `std/nat.sl`,
`std/list.sl` and `fourcolor/ring.sl`. The engines below are sketched in the same shape: **a macro that
wraps a `def-fns` (or a `def-adts`) and writes the body, consulting a hint table of lemma names that it
splices into the output.** Splicing names rather than passing lemmas as function values seems to avoid the
level restriction on calling functions held in data (WORKAROUNDS.md item 1). Several pass-2 reports
independently reached that conclusion, but nobody compiled it.

Two kinds of tactic show up:

- **Signature-in.** The user writes the statement and the tactic writes the proof. This is like
  `lt-lemma`, and it fits E3, E4 and most of E2.
- **Derive.** Given a `def-adts` and a mode (which indices are inputs), the tactic emits the standard kit
  of lemmas for that relation, signatures included: uniqueness, existence, inversion, length, append. This
  fits E1 and E2a, and corresponds to what other systems call derive handlers or scheme generation.

One limit, from DESIGN.md §65: a macro can `resolve` a name and compare or apply settled terms. Its list of
primitives does not seem to include "give me this ADT's constructors and their field types", and the
type of a local hypothesis is `RHypothetical`. So a derive-style tactic would apparently have to take the
raw `def-adts` form as its input (wrap it), and a signature-in tactic must read hypothesis types from the
signature's syntax, as `lt-lemma` does. This is unverified (§14).

## 4. E1: derive from a relation's definition

771 lemmas, 5,974 lines. Almost every lemma here is about a different relation; uniqueness alone is
written for about 150 relations. These are the most uniform lemmas in the proof.

**E1a — uniqueness: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `fn-sd` | 111 | 863 | 683 | 110 | 741 / 122 / 0 | 7 |
| `fn-subst` | 49 | 374 | 265 | 43 | 77 / 297 / 0 | 8 |
| `fn-guard` | 25 | 284 | 245 | 24 | 139 / 112 / 33 | 9 |
| `fn-inj` | 10 | 68 | 52 | 10 | 45 / 10 / 13 | 7 |
| `fn-agree` | 1 | 19 | 17 | 1 | 0 / 19 / 0 | 19 |
| **total** | **196** | **1608** | **1262** | | 1002 / 560 / 46 | |

**`fn-sd` — syntax-directed uniqueness.** Schema `R ins o1 -> R ins o2 -> o1 = o2`, where the input
indices pick the constructor. The skeleton: match both derivations, rewrite each premise's output with
that premise's `-fn` lemma by matching `Refl`, and return `Refl`. This covers finite tables (`addc-same`, 16
constructors), structural recursion (`snoc-fn`, `revapp-fn`), single-constructor records (`welt-fn`,
`graph-fn`) and multi-output records (`cb-fn`). Some groups are token-for-token identical once names are
normalised (`shift-fn`, `npl-fn`, `permt-fn`, `pairfrom-fn`); those make good regression targets.

```
(def-fns _ $ (erased snoc-fn : (erased Type A) (erased (List A) xs ys zs) (erased A a) (subterm erased (Snoc A xs a ys) p)
    (erased (Snoc A xs a zs) q) -> (erased (Eq (List A) ys zs) e))
  (let-match erased p (SnocCons _ _ _ xs1 ys1 p1) ((SnocNil _ _) (let-match erased q (SnocNil _ _)) (Refl _ ys)))
  (let-match erased q (SnocCons _ _ _ _ zs1 q1))
  (let-match erased (snoc-fn _ xs1 ys1 zs1 a p1 q1) (Refl _ _))
  (Refl _ ys))
```

- **Inputs:** the ADT, the mode, and a premise → `-fn` lemma hint map.
- **Hard parts:** rewrites must go in data-dependency order; tuple-returning hints; recursion on an
  index rather than the derivation (`pw3-fn`).

**`fn-guard`** is the same with overlapping constructors told apart by contradictory side premises. The
cross cases need `absurd` plus a refuter from a five-entry table (`apart-irrefl`, `notin-in`, `lt-asym`,
`lt-irrefl`, `pa-irrefl`), e.g. `bkmode-fn`, `hsum-fn`, `hemb-fn`. Small literal refutations (`Lt 2 0`) are
peeled by hand, presumably because numerals are opaque in types (WORKAROUNDS.md item 6).

**`fn-inj`** is the same tactic in the reverse mode (`snoc-inj`, `ncol-inj`).

**`fn-subst`** (counted here, found in the glue group) is the tactic's inner loop used on its own. Given
`R a b1` and `R a b2` in context, it emits `(let-match erased (R-fn ...) (Refl _ _))` and continues, as in
`bsp-lt`:

```
(def-fns _ $ (erased bsp-lt : (erased (Nat) k x lo hi v) (erased (Bsp k x lo hi) p) (erased (Pow2 k v) pv) -> (erased (Lt lo v) l))
  (let ((erased v2) (erased _) (erased pv2) (erased _) (erased _) (erased l)) (bsp-arith k x lo hi p))
  (let-match erased (pow2-fn k v v2 pv pv2) (Refl _ _))
  l)
```

That idiom appears in 115 forms of the glue group alone and throughout the rest. A "functional-dependency
saturation" step (rewrite to a fixed point, then close by assumption) would write those lines.

**E1b — existence (erased+runtime): subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `semi-syntax` | 35 | 607 | 555 | 35 | 244 / 298 / 65 | 12 |
| `rex-syntax` | 50 | 564 | 493 | 49 | 252 / 312 / 0 | 8 |
| `ex-sd` | 84 | 531 | 422 | 69 | 459 / 72 / 0 | 6 |
| `chk-record` | 35 | 391 | 347 | 34 | 157 / 218 / 16 | 9 |
| `ex-pre` | 16 | 144 | 113 | 15 | 0 / 112 / 32 | 8 |
| `exists-chk` | 14 | 130 | 110 | 13 | 62 / 68 / 0 | 8 |
| `ex-fin` | 21 | 110 | 89 | 20 | 81 / 29 / 0 | 4 |
| `ex-guard` | 15 | 109 | 89 | 15 | 109 / 0 / 0 | 7 |
| `forall-chk` | 15 | 102 | 82 | 15 | 72 / 30 / 0 | 6 |
| `ex-plus` | 8 | 60 | 42 | 6 | 0 / 47 / 13 | 7 |
| `ex-const` | 11 | 41 | 29 | 10 | 41 / 0 / 0 | 3 |
| `parse` | 6 | 37 | 31 | 6 | 37 / 0 / 0 | 7 |
| `semi-by-compute` | 7 | 32 | 25 | 6 | 32 / 0 / 0 | 5 |
| `ex-wf` | 2 | 13 | 10 | 2 | 0 / 0 / 13 | 8 |
| **total** | **319** | **2871** | **2437** | | 1546 / 1186 / 139 | |

**`ex-sd` — syntax-directed existence.** Schema `∀ ins. ∃ o. R ins o` by recursion that mirrors R's
constructors, filling each premise from a hint (`P-exists`, `nth-exists`, or a primitive `add`):

```
(def-fns _ $ (erased snoc-exists : (erased Type A) (subterm erased (List A) xs) (erased A a) ->
    (erased (List A) ys) (erased (Snoc A xs a ys) s))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values (Cons _ a (Nil _)) (SnocNil _ a))))
  (let ((erased ys1) (erased s1)) (snoc-exists _ xs1 a))
  (values (Cons _ x ys1) (SnocCons _ x a xs1 ys1 s1)))
```

Its variants differ only in how a premise is filled:
- **`ex-guard`:** the constructor is chosen by a decider (`in-dec`, `nat-cmp`).
- **`ex-fin`:** a finite input is enumerated.
- **`ex-const`:** the output is a given term.
- **`ex-pre`:** a partial relation is made total under a bound, with Nil refuted against the bound.
- **`ex-plus`:** an invariant is returned as well.

**The runtime twins.** `rex-syntax`, `semi-syntax`, `chk-record`, `forall-chk`, `exists-chk`, `parse`
and `semi-by-compute` were first bucketed as "reflection checkers". On a second reading they turned out to
be the same generator in `many` mode: each returns a runtime value with an erased derivation of R itself.
`semi-syntax` and friends add a failure branch (`ErasedMaybe`, `IfT`, or a bespoke Yes/No type). Because the
result type is R itself, there is no separate soundness lemma to pair with them. Several relations have
both modes written out (`snoc-exists`/`snoc-c`, `lapp-make`/`lapp-c`, `length-exists`/`size-c`,
`permt-ex`/`permt-c`), and In/NotIn has three deciders (`in-dec`, `in-dec-c`, `in-q`). One generator
with a mode flag (erased/many) and a carrier flag (total/partial) covers both halves. Pass 2 likened it
to a mode-directed predicate compiler.

What it cannot do:
- choose heuristically when several constructors apply (`insert` uses `layer-after`);
- consult untrusted oracle programs whose output is re-checked (`refute-c` with `plan-c`, `qzcert-c` with
  `mark-all`). A generator could accept "oracle" hint entries for these, but it is not mechanical.

**E1c — inversion: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `inv-xlate` | 69 | 354 | 236 | 60 | 163 / 191 / 0 | 5 |
| `inv-ctor` | 47 | 255 | 164 | 41 | 152 / 103 / 0 | 5 |
| `inv-proj` | 23 | 108 | 60 | 18 | 93 / 15 / 0 | 5 |
| `inv-pin` | 14 | 79 | 58 | 13 | 44 / 35 / 0 | 6 |
| `inv-refute` | 11 | 60 | 46 | 11 | 40 / 20 / 0 | 4 |
| **total** | **164** | **856** | **564** | | 492 / 364 / 0 | |

**What the subcategories are:**
- **`inv-ctor`:** `R (C ..) -> premise`, i.e. inversion at a constructor-shaped index (`moves-tail`, `chain-head`).
- **`inv-proj`:** the single-constructor case, i.e. record field projection. Pass 2 suggests these be
  generated with the type as accessors, which makes them library rather than tactic.
- **`inv-pin`:** a constant index forces equalities (`bc-zero`: `BitCons m b Zero -> m = 0, b = Bit0`).
- **`inv-refute`:** R at an impossible index gives False (`occ3-empty`, `sub-empty`).
- **`inv-xlate`:** a constructor-to-constructor case map into another relation (`push-depth`, `sep-sym`).
  It is the non-recursive half of E2b's `convert`.

All are emitted from the ADT given an index pattern, except `inv-xlate`, which needs the constructor map
(often inferable by unification).

**E1d — decidability+negation: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `neg-by-cases` | 23 | 152 | 104 | 18 | 0 / 69 / 83 | 6 |
| `dec-lift` | 17 | 133 | 109 | 15 | 114 / 19 / 0 | 7 |
| `dec-fin` | 10 | 89 | 79 | 10 | 32 / 57 / 0 | 12 |
| `neg-excl` | 14 | 63 | 42 | 14 | 63 / 0 / 0 | 5 |
| `dec-ans` | 6 | 57 | 46 | 5 | 0 / 57 / 0 | 11 |
| `dec-ord` | 7 | 44 | 37 | 7 | 44 / 0 / 0 | 7 |
| `dec-eq` | 3 | 30 | 26 | 3 | 30 / 0 / 0 | 10 |
| `neg-fn-clash` | 6 | 28 | 17 | 6 | 18 / 10 / 0 | 5 |
| `filter-chk` | 3 | 23 | 20 | 3 | 16 / 7 / 0 | 7 |
| `eq-chk` | 2 | 12 | 10 | 2 | 12 / 0 / 0 | 7 |
| `neg-build` | 1 | 8 | 6 | 1 | 0 / 8 / 0 | 8 |
| **total** | **92** | **639** | **496** | | 329 / 227 / 83 | |

Negation in this proof is carried by first-order certificates (`NotIn`, `Apart`, `BadAt`, ...). So a
decidable property usually comes as a complementary pair P/Q, with three lemmas around it:

- **`dec-lift`:** `Or (P xs) (Q xs)` by recursion with a pointwise decider (`in-dec`, `sub-dec`, `fit-dec`);
- **`neg-excl`:** `P x -> Q x -> False` (`in-notin`, `allnz-hasc0`);
- often a runtime semi-decider as well (E1b).

Eleven families have both the decider and the exclusion lemma written by hand (In, Pw, InRg, FitSec,
Flag, ...). A complementary-pair derivation would emit them together.

**`neg-fn-clash`** (`R x a -> R x b -> Apart a b -> False`) is a one-line corollary of each `-fn` lemma and
could be emitted alongside it.

**`neg-by-cases`** (decide, then refute one branch) has a generic scaffold but a per-lemma refutation, so
it is a macro rather than a tactic.

## 5. E2: structural rebuild

1,170 lemmas, 8,137 lines, the largest engine. Pass 2 found one proof shape under nearly all of it:

> structural recursion on one `subterm` derivation D; in each case, invert the other derivations that
> share D's spine in lockstep; fill each premise of the target constructor with a hint lemma chosen by
> type; recurse; rebuild the target constructor (or return via `values`).

The subcategories differ in how the target is found from the source. The recommendation is one engine
with a front end per subcategory.

**E2a — list-builder algebra: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `op-join` | 87 | 618 | 423 | 70 | 233 / 334 / 51 | 6 |
| `op-split` | 28 | 220 | 156 | 23 | 76 / 133 / 11 | 7 |
| `length` | 37 | 199 | 128 | 36 | 125 / 74 / 0 | 5 |
| `mem-thru-builder` | 25 | 165 | 116 | 14 | 126 / 39 / 0 | 6 |
| `forall-thru-builder` | 24 | 146 | 106 | 15 | 140 / 6 / 0 | 6 |
| `fn-graph-algebra` | 24 | 135 | 89 | 9 | 135 / 0 / 0 | 6 |
| `nth-thru-builder` | 13 | 96 | 69 | 7 | 48 / 48 / 0 | 7 |
| `equiv` | 19 | 92 | 58 | 15 | 56 / 36 / 0 | 5 |
| `length-thru-builder` | 10 | 82 | 62 | 7 | 53 / 29 / 0 | 8 |
| `forall-pointwise` | 9 | 40 | 26 | 3 | 20 / 20 / 0 | 4 |
| `fold-thru-builder` | 4 | 32 | 24 | 1 | 0 / 32 / 0 | 7 |
| `map-mem` | 4 | 31 | 23 | 2 | 14 / 17 / 0 | 7 |
| `nth-mem-bridge` | 5 | 20 | 13 | 5 | 20 / 0 / 0 | 4 |
| `map-compose` | 3 | 17 | 10 | 1 | 9 / 8 / 0 | 5 |
| **total** | **292** | **1893** | **1303** | | 1055 / 776 / 62 | |

The relation is carried through a list operation: Snoc, LApp, RevApp, Cat, Ins, Split, Repeat, SetNth
and Rots. The two ADTs fully determine the proof, so no hint table is needed for Forall-shaped relations.

- **`op-join`/`op-split`:** `R xs -> R ys -> LApp xs ys zs -> R zs` and its inverse. Joins: Snoc 27,
  LApp 19, RevApp 8, Repeat 7, Cat 6, SetNth 5, Rots 5.
- **`length`:** `R xs ys -> Length xs n -> Length ys n`, restated for about 36 relations, as in
  `respects-length`:

```
(def-fns _ $ (erased respects-length : (erased (List (Nat)) lab xs ls) (erased (Nat) n) (subterm erased (Respects lab xs ls) rp)
    (erased (Length (Nat) xs n) l) -> (erased (Length (Nat) ls n) r))
  (let-match erased rp (RespCons _ xs1 ls1 _ v _ rp1) ((RespNil _) (let-match erased l (LengthNil _)) (LengthNil _)))
  (let-match erased l (LengthCons _ _ _ n1 l1))
  (LengthCons _ v ls1 n1 (respects-length lab xs1 ls1 n1 rp1 l1)))
```

- **The `*-thru-builder` families** are membership, Forall, Nth or Length facts pushed through a builder.
  `In` (Nat only), `Elem` (polymorphic) and `Adj` (In on bonds) each get their own copy of the same three
  append lemmas, e.g. `mem-left`, `app-in-l` and `adj-cat-l` for "member of the left part".
- **`fn-graph-algebra`:** associativity, units and rev/snoc interchange of LApp/Snoc/RevApp as relations.
- **`equiv`:** reflexivity, symmetry and transitivity of pointwise relations (`link-refl/sym/trans`).

Generic versions of some of these already exist (`plan.sl`'s `allr-split/join`, `pw-split/join`,
`ringtrace.sl`'s `all2-length`, `all2-revapp`) and give a ground truth to diff a generator against.

**What it cannot do:**
- RevApp's accumulator needs a generalised invariant (`Or (P pre) (P acc)`), which the user must declare.
- Lay/Flatten layouts need per-block shift lemmas.
- Distinct needs the NotIn instance for the same builder first, so generation has an ordering.

**E2b — transport/convert: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `transport` | 127 | 806 | 540 | 93 | 292 / 470 / 44 | 5 |
| `convert` | 122 | 804 | 516 | 72 | 207 / 456 / 141 | 6 |
| `combine` | 74 | 568 | 405 | 47 | 95 / 350 / 123 | 7 |
| `rec-map` | 66 | 449 | 299 | 47 | 160 / 272 / 17 | 6 |
| `exists-map` | 21 | 199 | 139 | 14 | 6 / 122 / 71 | 9 |
| `rec-convert` | 27 | 169 | 109 | 21 | 57 / 112 / 0 | 5 |
| `conv-iso` | 31 | 169 | 113 | 25 | 97 / 72 / 0 | 5 |
| `conv-acc` | 13 | 124 | 98 | 12 | 0 / 64 / 60 | 7 |
| `build` | 13 | 116 | 90 | 8 | 20 / 81 / 15 | 7 |
| `sym-transport` | 13 | 71 | 39 | 9 | 55 / 16 / 0 | 5 |
| `aggregate` | 5 | 36 | 27 | 5 | 0 / 36 / 0 | 7 |
| `rec-reindex` | 10 | 31 | 20 | 9 | 25 / 6 / 0 | 3 |
| `conv-zip` | 3 | 20 | 14 | 3 | 20 / 0 / 0 | 7 |
| **total** | **525** | **3562** | **2409** | | 1034 / 2057 / 471 | |

**`transport`:** same relation and spine, with a non-spine parameter changing (`*-weaken`, `*-move`,
`*-grow`, `*-ext`). Each premise is carried across by one hint lemma:

```
(def-fns _ $ (erased walk-weaken : (erased (List (Nat)) e nd s s2) (erased (Nat) a b) (subterm erased (Walk e nd s a b) w)
    (erased (HSub s2 s) sb) -> (erased (Walk e nd s2 a b) r))
  (let-match erased w (WalkStep _ _ _ _ q c _ pe pn out w1) ((WalkHere _ _ _ _) (WalkHere e nd s2 a)))
  (WalkStep e nd s2 a q c b pe pn (notin-sub q s2 s sb out) (walk-weaken e nd s s2 c b w1 sb)))
```

**`convert`:** a different relation over the same spine (`R xs -> R' xs`; `under-sub`, `rooted-covers`).
Contrapositive targets such as `Under -> NotIn` are common.

**`combine`:** two derivations over one spine inverted in lockstep, giving a third relation
(`fixed-third`) or a Forall2 composition (`Respects` dominates).

**`exists-map`:** the functorial map with existence, `All P xs -> (∀x. P x -> ∃y. Q x y) -> ∃ys. All2 Q xs ys`.

**`build`:** construction from a bare list.

**`rec-map`, `rec-reindex`, `rec-convert` and `sym-transport`** are the non-recursive record versions,
found in the glue group:
- `rec-map` rebuilds one record with each field moved by its own relation's hint (`link-weaken`,
  `disk-move`).
- `rec-reindex` permutes a record's indices; the field permutation is forced by types (`hyper-rot`):

```
(def-fns _ $ (erased hyper-rot : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) -> (erased (Hypermap d n f e) r))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (MkHypermap d n f e ids en nf fe io cen kn cnf kf cfe ke))
```

- `sym-transport` is "without loss of generality by symmetry". It applies a lemma at a rotated instance
  and rotates back using the `rec-reindex` lemmas as the group action.

Several `rec-map` groups are the same change at different records. Along `HSub` there are `disk-move`,
`fband-move` and `fe-move`; along one tree step `CtSel` there are `mem-cons`, `pm-lift`, `both-lift`,
`keep-lift` and `gone-lift`.

**What it cannot do:**
- Nodes that need a case split (`nr-insert` via `nat-cmp`).
- Tree-shaped relations with 3–6 recursive calls (`CtOr`, `CtPerm`); these need n-ary support.
- Mutual relations (`FlB`/`KF`, `NIv`/`NIvK`).

Many L-rated lemmas here have the generic skeleton but a node step that is a 3–15-lemma domain argument
(patch.sl, kempemap.sl). Pass 2 suggests a convention of one named node lemma per relation (`T-at`), which
would turn those into H.

**E2c — Forall elimination: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `fa2-nth` | 23 | 153 | 103 | 19 | 125 / 28 / 0 | 6 |
| `fa-multi` | 16 | 152 | 120 | 13 | 67 / 69 / 16 | 9 |
| `fa-in` | 26 | 113 | 65 | 25 | 113 / 0 / 0 | 4 |
| `fa-adj` | 10 | 94 | 74 | 8 | 54 / 40 / 0 | 6 |
| `fa2-in` | 8 | 63 | 45 | 6 | 52 / 11 / 0 | 8 |
| `tab-idx` | 9 | 59 | 40 | 9 | 42 / 17 / 0 | 6 |
| `fa-nth` | 11 | 57 | 34 | 10 | 57 / 0 / 0 | 5 |
| `fa-tree` | 5 | 53 | 42 | 4 | 16 / 37 / 0 | 11 |
| `fa-post` | 5 | 47 | 35 | 5 | 0 / 37 / 10 | 10 |
| `fa-nth-acc` | 6 | 42 | 30 | 6 | 20 / 22 / 0 | 7 |
| `tab-in` | 4 | 24 | 16 | 2 | 12 / 12 / 0 | 6 |
| `fa-nest` | 2 | 11 | 7 | 2 | 6 / 5 / 0 | 6 |
| `fa-pair` | 1 | 7 | 5 | 1 | 0 / 7 / 0 | 7 |
| `fa-misc` | 1 | 5 | 3 | 1 | 0 / 0 / 5 | 5 |
| **total** | **127** | **880** | **619** | | 564 / 285 / 31 | |

A Forall-like ADT is eliminated at a membership witness (`In`, `Elem`, `Nth`, `Adj`, or a counted index)
to get the element's fact:

```
(def-fns _ $ (erased reducible-mem : (erased (Level) X) (erased (Config) cf) (erased (List (Config)) cfs) (subterm erased (AllRed X cfs) a)
    (erased (Elem (Config) cf cfs) m) -> (erased (Reducible X cf) r))
  (let-match erased a (AllRedCons _ _ rest rd a1) (absurd (AllRedNil _) m))
  (match erased m _
    ((ElHere _ _ _) rd)
    ((ElThere _ _ _ _ m1) (reducible-mem X cf rest a1 m1))))
```

Every pass-1 agent invented this bucket independently, under five different names.

- **`fa-in`/`fa-nth`:** a 5–7-line skeleton identical across 35 relations, needing no hints.
- **`fa2-nth`/`fa2-in`:** the aligned two-list versions, which return the partner's Nth.
- **`fa-adj`:** over bond lists; the backward case needs the element relation's symmetry lemma.
- **`fa-multi`:** relations with several cons constructors (filters, partitions). These return an
  `Or` or refute a constructor, so they need a per-constructor hint.
- **`tab-*`:** counted tables, `T m n -> m ≤ i < n -> P i`, with an arithmetic refuter.

`Respects` alone has six near-duplicate eliminators across files (`respects-nth`, `resp-at`,
`respects-at`, `in-label`, `fixed-in`, `respects-val`).

**E2d — paths/closures: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `clos-fold` | 49 | 351 | 250 | 27 | 119 / 177 / 55 | 6 |
| `clos-simulate` | 16 | 159 | 114 | 9 | 0 / 102 / 57 | 9 |
| `clos-split` | 10 | 82 | 58 | 4 | 12 / 45 / 25 | 8 |
| `clos-cat` | 15 | 74 | 45 | 14 | 69 / 5 / 0 | 5 |
| `clos-lift` | 12 | 73 | 46 | 7 | 35 / 19 / 19 | 5 |
| `chain-rtc` | 7 | 44 | 30 | 7 | 22 / 22 / 0 | 7 |
| `clos-inv` | 7 | 32 | 17 | 2 | 16 / 16 / 0 | 4 |
| `clos-snoc` | 5 | 31 | 20 | 5 | 22 / 9 / 0 | 6 |
| `clos-mem` | 3 | 24 | 18 | 2 | 0 / 24 / 0 | 8 |
| `clos-unsnoc` | 2 | 20 | 14 | 2 | 0 / 20 / 0 | 13 |
| `clos-intro` | 3 | 8 | 5 | 3 | 4 / 4 / 0 | 2 |
| `clos-sym` | 1 | 3 | 2 | 1 | 3 / 0 / 0 | 3 |
| **total** | **130** | **901** | **619** | | 302 / 443 / 156 | |

**The closure kit:** `clos-cat`, `clos-snoc`, `clos-intro`, `clos-sym`, `clos-unsnoc` and `chain-rtc`.
Given a closure ADT with a reflexive constructor and step constructors, emit concatenation, snoc, inclusion
and symmetry. This is written for Conn, Path, CPath, RPath, SDPath, XP, DPath, Iter, FaceReach, FR and
NodeReach:

```
(def-fns _ $ (erased conn-cat : (erased (List (Bond)) g) (erased (Nat) x y z) (subterm erased (Conn g x y) c) (erased (Conn g y z) d)
    -> (erased (Conn g x z) r))
  (let-match erased c (ConnStep _ _ w _ a c1) ((ConnHere _ _) d))
  (ConnStep g x w z a (conn-cat g w y z c1 d)))
```

**The catamorphisms:** `clos-fold`, `clos-inv` and `clos-lift`. They fold a named one-step lemma along a
path: `P x -> Path x y -> P y` (`order-path`, `ker-path`), or map a path into another closure.
`clos-simulate` adds an image path returned existentially.

**What stays by hand:** `clos-split` (split a path at a member, cut at first visit) is mostly M because each
instance has its own extra outputs.

**E2e — frames: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `frame-tree` | 11 | 202 | 73 | 9 | 23 / 59 / 120 | 17 |
| `array-frame` | 14 | 109 | 82 | 8 | 61 / 48 / 0 | 6 |
| `frame-seq` | 12 | 77 | 49 | 10 | 31 / 24 / 22 | 5 |
| `frame-upd` | 5 | 40 | 28 | 5 | 23 / 17 / 0 | 6 |
| `frame-cell` | 5 | 33 | 21 | 3 | 23 / 10 / 0 | 6 |
| `frame-range` | 6 | 29 | 17 | 5 | 29 / 0 / 0 | 5 |
| **total** | **53** | **490** | **270** | | 190 / 158 / 142 | |

All in `red/r4*.sl`. An array invariant survives a write (`SetNth`, `Put`) outside its footprint.
- **`frame-cell` and `frame-range`** are mechanical given the write's "other index" lemma.
- **`frame-seq`** folds a single-write lemma over a write list; it has the same catamorphism shape as
  `clos-fold`.
- **`frame-tree`** has mutual tree invariants (`Lz`/`LzK`, `NIv`/`NIvK`, `NPart`/`NPartK`). The skeleton
  is mechanical, but the footprint split per child is not, and about 120 of its lines stay L.

**E2f — functions/tries: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `convert-fun` | 34 | 316 | 216 | 14 | 9 / 147 / 160 | 9 |
| `tree-descend` | 9 | 95 | 74 | 9 | 0 / 95 / 0 | 10 |
| **total** | **43** | **411** | **290** | | 9 / 242 / 160 | |

**`convert-fun`:** a property of a graph or colouring is lifted along `Fun p g`, into Const, Spans,
BondsBelow and others. The skeleton is always the same, but the node fact is often a multi-lemma domain
argument.

**`tree-descend`:** a trie invariant is pushed down an address list (`red/r4c.sl`, `red/flat.sl`). It is a
`clos-fold` where the path is an address, with a 4–6-way selector match per step.

## 6. E3: decision procedures

455 lemmas, 3,774 lines.

**E3a — enum decide: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `enum-table` | 82 | 633 | 524 | 26 | 436 / 197 / 0 | 5 |
| `enum-inversion` | 15 | 356 | 322 | 12 | 0 / 144 / 212 | 16 |
| `enum-code` | 25 | 143 | 109 | 15 | 117 / 26 / 0 | 5 |
| `ground-witness` | 14 | 131 | 110 | 11 | 77 / 54 / 0 | 7 |
| `small-list` | 8 | 77 | 62 | 6 | 21 / 56 / 0 | 8 |
| `prop-case` | 2 | 33 | 24 | 1 | 0 / 33 / 0 | 18 |
| **total** | **146** | **1373** | **1151** | | 651 / 510 / 212 | |

**`enum-table`:** laws of operation tables over small enums: ColAdd, AddK, Xor, PermC, Third and
BitApply. Commutativity, associativity, cancellation, inverses and existence are all proved by hand as
case trees. `addc-comm` (`cfcolor.sl`) is 18 lines of 16 cases. `permc-add` is 105 lines. The Klein-group
laws are written twice, once for `ColAdd` and once for `AddK`, which look like the same relation. A
`decide` tactic splits on hypotheses' constructors, lets forcing refute impossible combinations, and
searches the goal relation's constructors. It needs no lemma calls at all.

**Wider variants:**
- **`enum-code`:** enum ↔ Nat codes.
- **`enum-inversion`:** case trees mixing enum and non-enum indices; L-heavy.
- **`small-list`:** lists of known fixed length.
- **`ground-witness`:** closed concrete objects such as initial maps, `plane-nil` and `cpmap0`.

These widen the same engine with a hint table.

**A caveat:** a full case tree may be large (`permc-add` has about 6×16 leaves), and its elaboration time
is unmeasured.

**E3b — linear arithmetic: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `lin-record` | 53 | 371 | 288 | 25 | 199 / 172 / 0 | 5 |
| `lin-arith` | 17 | 273 | 225 | 8 | 95 / 178 / 0 | 12 |
| `nat-lib` | 42 | 186 | 126 | 6 | 186 / 0 / 0 | 4 |
| `fnrel-mono` | 24 | 124 | 93 | 11 | 93 / 31 / 0 | 5 |
| `struct-bound` | 14 | 118 | 93 | 13 | 27 / 91 / 0 | 9 |
| `numeral` | 12 | 100 | 85 | 6 | 91 / 0 / 9 | 3 |
| `fnrel-conv` | 20 | 99 | 75 | 10 | 77 / 22 / 0 | 5 |
| `nonlin-ring` | 6 | 86 | 62 | 6 | 20 / 46 / 20 | 14 |
| `const-bound` | 11 | 39 | 28 | 10 | 18 / 21 / 0 | 3 |
| `ac-eq` | 6 | 36 | 27 | 2 | 29 / 7 / 0 | 7 |
| `order-lib` | 7 | 28 | 21 | 3 | 28 / 0 / 0 | 4 |
| **total** | **212** | **1460** | **1123** | | 863 / 568 / 29 | |

**What the subcategories are:**
- **`nat-lib`:** Add/Mul/Lt laws, mostly in ring.sl already. It is the axiom base, not a tactic target,
  and it holds about 10 restatements under other names (`add-one-r`/`add1`, `plus-lcomm`/`add-right-comm`).
- **`lin-arith`:** linear (in)equalities from Add/Lt/Mul-by-literal hypotheses.
- **`lin-record`:** unpack a record of linear facts (EulerSum, Rmd, InRg), solve, and repack.
- **`fnrel-conv`/`fnrel-mono`:** functions written as relations (Thrice, Double, Pw3, Monus, Mx, BnB),
  each with its own conversion and monotonicity lemmas.
- **`numeral`/`const-bound`:** facts about literals. These exist because numerals are opaque in types.

**What `fourcolor/ring.sl` already is:** a working reflective normaliser for commutative-semiring
equalities over Nat (`Expr`, `Eval`, `norm`, `ring-check`, `ring-sound`), used at about 10 sites. At those
sites most of the hand work is building the `Eval` derivations. `genus-arith`'s 81 lines are mostly
reification plus a hand-made linear combination. `EvNum` takes a literal directly, so reified goals seem
to sidestep numeral opacity.

**Extensions in order of payoff** (pass-2 estimates, unverified):

1. **Auto-reification:** a macro wrapping the `def-fns` reads Add/Mul hypotheses from the signature's
   syntax and emits the `Eval` derivations.
2. **Linear combination plus cancellation:** check `a + Σcᵢbᵢ ≡ b + Σcᵢaᵢ` by `ring-check`, then
   `add-cancel`.
3. **Inequalities via slack:** `Lt a b ⇔ ∃d. a + Succ d = b`, with the leftover polynomial as the witness.
4. **A hint table of reification adapters** for Double, Thrice and multiplication by a literal.

With all four, about 1,000–1,100 of the ~1,900 Nat-arithmetic lines are covered. Radix, BITS and FIN are
not reached.

**E3c — positional numerals/bits: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `radix` | 28 | 273 | 223 | 12 | 78 / 164 / 31 | 7 |
| `bits-radix` | 35 | 272 | 222 | 7 | 72 / 200 / 0 | 7 |
| `word-field` | 19 | 214 | 174 | 9 | 9 / 171 / 34 | 11 |
| `bw-pointwise` | 15 | 182 | 160 | 4 | 24 / 158 / 0 | 11 |
| **total** | **97** | **941** | **779** | | 183 / 693 / 65 | |

`radix` (base 3: `x = q·d + r`, Kid, RIdx, Pw3) and `bits-radix` (base 2: Bsp, BitCons, Pow2) are one
theory at two bases. `word-field` is bits-radix plus an `enum-table` step per bit; `bw-pointwise` is a
structural recursion over Bitwise with a truth-table step. Pass 2 judged a single parametric
positional-numeral library a better fit than a tactic (§10). The 4-bit fields could alternatively be
proved by exhaustion over 16 values.

## 7. E4: hint search

268 lemmas, 1,567 lines, all found in the glue group.

**E4 — hint search (eauto): subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `case-dispatch` | 54 | 393 | 276 | 45 | 84 / 309 / 0 | 7 |
| `chain` | 83 | 389 | 196 | 51 | 214 / 175 / 0 | 4 |
| `exists-close` | 61 | 348 | 224 | 43 | 240 / 108 / 0 | 5 |
| `ctor-fill` | 43 | 256 | 147 | 33 | 150 / 106 / 0 | 5 |
| `cover-refute` | 22 | 152 | 104 | 16 | 81 / 71 / 0 | 7 |
| `or-map` | 5 | 29 | 16 | 4 | 29 / 0 / 0 | 6 |
| **total** | **268** | **1567** | **963** | | 798 / 769 / 0 | |

**What the subcategories are:**
- **`chain`:** pure backward chaining through 2–5 lemmas. `geo.sl`'s `geo-k1`..`geo-k9` are nine
  configuration leaves filled from the same four lemmas.
- **`exists-close`:** obtain witnesses from `*-exists`, then apply one lemma. `perm-fix2` is an example:

```
(def-fns _ $ (erased perm-fix2 : (erased (Nat) d) (erased (List (Nat)) p q p2) (erased (HPerm d p q) pm) (erased (Snoc (Nat) p d p2) s)
    -> (erased (List (Nat)) q2) (erased (HPerm (Succ d) p2 q2) r))
  (let ((erased q2) (erased sq)) (snoc-exists _ q d))
  (values q2 (perm-fix d p q p2 q2 pm s sq)))
```

- **`ctor-fill`:** a constructor tree whose premises come from hypotheses. The closed `OrderOf` builders
  are written five times: `order1`, `order2`, `order-of-two`, `order-of-three` and `mk-order3`.
- **`cover-refute`:** call a covering lemma, refute every arm but one with the NEG lemmas, and return
  the live arm.
- **`case-dispatch`:** `destruct`, then one lemma per arm.
- **`or-map`:** `Or A B -> (A→A') -> (B→B') -> Or A' B'`, instantiated by hand five times.

**The engine:** one depth-bounded search over a hint table would be the back end for all of these. That
table holds the goal relation's constructors, the `*-exists` lemmas, the record projections and a
per-file list. The same engine would also serve E2's side goals.

**The hard part:** arguments are explicit and positional, so the search must also synthesise every index
argument. How far `_` inference (DESIGN.md §50) already covers that was not checked.

**A note on scope:** many `chain` and `exists-close` lemmas are used once. With a search tactic they
would be inlined at the caller. Without one, they are reasonable named proof steps rather than waste.

## 8. E5: reflection, soundness and bespoke checkers

88 lemmas, 1,439 lines, mostly M/L. This is less uniform than first thought.

**E5 — reflection: soundness+bespoke checkers: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `sound-fold` | 18 | 392 | 331 | 18 | 5 / 285 / 102 | 18 |
| `semi-fuel` | 12 | 234 | 216 | 11 | 14 / 220 / 0 | 15 |
| `rex-builder` | 15 | 218 | 182 | 8 | 23 / 165 / 30 | 12 |
| `sound-sim` | 8 | 217 | 194 | 8 | 0 / 217 / 0 | 21 |
| `sound-unpack` | 11 | 148 | 113 | 11 | 8 / 71 / 69 | 10 |
| `sound-refute` | 6 | 114 | 100 | 6 | 5 / 109 / 0 | 23 |
| `prim-wrap` | 6 | 40 | 29 | 5 | 0 / 40 / 0 | 6 |
| `chk-run` | 8 | 31 | 23 | 5 | 23 / 8 / 0 | 5 |
| `reflect-quote` | 3 | 27 | 18 | 3 | 27 / 0 / 0 | 10 |
| `reify-index` | 1 | 18 | 16 | 1 | 0 / 18 / 0 | 18 |
| **total** | **88** | **1439** | **1222** | | 105 / 1133 / 201 | |

**`sound-fold`:** a catamorphism of a certificate ADT R into a semantic statement, `R x -> H x -> S x`,
one per-constructor hint each. Examples: `insert-sound` and `eval-norm` in ring.sl, `rwalk-sound` (67
lines, mostly one propagation repeated per constructor), and `sr-count`. About 15 relations have both a
runtime builder (E1b) and a fold, so a single `derive R check sound` with both hint tables would generate
both halves (Ins/Norm, CtOr/CtPerm, Sr, Implied, Db1/Db2, RWalk/REst, Conv*, Pres, RedD).

**`sound-sim`:** the per-constructor hints themselves. They are short domain proofs, so the tactic can emit
the case split and the inversions but not the bodies.

**`sound-refute`:** `sound-fold` with motive False, over No-certificates (`NoExt`, `RTNo`, `Refut`).

**`semi-fuel` and `rex-builder`:**
- `semi-fuel` is fuelled search steered by untrusted planners.
- `rex-builder` is certified constructors that thread domain invariants (`cpcol-c`, 82 lines).

Both are left by hand.

No completeness lemma (No implies not R) exists anywhere: the design is soundness-only. The ring pipeline
(`norm`, `ring-check`, `eval-norm`, `ring-sound`, plus the quote half `shoe-ev`/`ev-dot`) is the one
complete classic reflection stack, and a better candidate for a one-time library tactic than for a
generator.

## 9. Not tactics: ergonomics, residue, duplicates

**L — language/ergonomics: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `field-lift` | 165 | 956 | 612 | 87 | 521 / 435 / 0 | 5 |
| `rec-proj-call` | 21 | 145 | 99 | 18 | 38 / 107 / 0 | 6 |
| `bundle` | 13 | 118 | 74 | 13 | 38 / 80 / 0 | 7 |
| `specialise` | 18 | 61 | 24 | 17 | 61 / 0 / 0 | 3 |
| `rec-proj` | 4 | 26 | 14 | 4 | 20 / 6 / 0 | 8 |
| `rec-regroup` | 2 | 10 | 4 | 1 | 10 / 0 / 0 | 5 |
| **total** | **223** | **1316** | **827** | | 688 / 628 / 0 | |

**`field-lift`:** unpack one record, pass one to three fields to one lemma and return, as in `ker-of`:

```
(def-fns _ $ (erased ker-of : (erased (Nat) d x) (erased (List (Nat)) f r as) (erased (KernelList d f r as) kl) (erased (In x as) ix) -> (erased (Kernel f r x) k))
  (let-match erased kl (MkKernelList _ _ _ _ _ _ ka _))
  (kerall-in f r as x ka ix))
```

- **How common positional patterns are:** 182 forms in the glue group contain a record pattern of 10 or
  more slots that is at least half `_`.
- **What would remove them:** named field projection in expressions, plus named or nested record fields.
  This is language ergonomics, not a tactic.
- **Which of them to keep:** some (`perm-nth`, `upd2-*`, `edge-old`) are a record's real API, reused
  often, and fine as library lemmas. The once-used adapters on context records (`rds-*`, `ker-*` on
  `EEnv`/`TCx`) are the removable ones.

**`bundle`:** return several unrelated facts as a tuple.

**`specialise`:** a lemma restated at fixed arguments. Optional or default arguments would remove these.

**X — other residue: subcategories** (lines exclude rows reassigned in pass 2)

| subcategory | lemmas | lines | body lines | relations | H / M / L lines | median |
|---|---|---|---|---|---|---|
| `rot-transport` | 19 | 169 | 123 | 16 | 18 / 109 / 42 | 9 |
| `level-factory` | 7 | 79 | 61 | 7 | 79 / 0 / 0 | 10 |
| `rot-structure` | 4 | 76 | 69 | 4 | 0 / 32 / 44 | 15 |
| `dup-param` | 9 | 56 | 36 | 6 | 56 / 0 / 0 | 6 |
| `dup-mirror` | 3 | 51 | 44 | 3 | 5 / 46 / 0 | 17 |
| `rotate-invariance` | 6 | 38 | 27 | 3 | 30 / 8 / 0 | 6 |
| `level-glue` | 2 | 37 | 33 | 2 | 37 / 0 / 0 | 28 |
| `concrete-prefix` | 3 | 34 | 25 | 1 | 10 / 24 / 0 | 10 |
| `array-glue` | 4 | 33 | 24 | 2 | 0 / 33 / 0 | 7 |
| `pigeonhole` | 3 | 33 | 27 | 3 | 0 / 33 / 0 | 10 |
| `map-inj` | 2 | 28 | 24 | 2 | 0 / 28 / 0 | 15 |
| `fn-classify` | 1 | 28 | 26 | 1 | 0 / 28 / 0 | 28 |
| `sorted-pw` | 3 | 25 | 19 | 1 | 0 / 25 / 0 | 6 |
| `dup-variant` | 3 | 23 | 14 | 2 | 6 / 17 / 0 | 8 |
| `iota` | 3 | 18 | 14 | 1 | 3 / 15 / 0 | 7 |
| `decompose-exists` | 3 | 16 | 11 | 2 | 16 / 0 / 0 | 6 |
| `nth-core` | 1 | 12 | 10 | 1 | 12 / 0 / 0 | 12 |
| `level-lift` | 2 | 10 | 6 | 2 | 10 / 0 / 0 | 5 |
| `dup-exact` | 1 | 4 | 3 | 1 | 4 / 0 / 0 | 4 |
| **total** | **79** | **770** | **596** | | 286 / 398 / 86 | |

**Rotations:** `rot-transport`, `rot-structure` and `rotate-invariance`. A list-indexed structure is
transported along a rotation (`R (x::xs) -> Snoc xs x ys -> R ys`), per record (RingOK, KMatch, LRT, UTr,
CpCol). Pass 2 notes that indexing rings by a cyclic-list type up to rotation might remove most of these
(§10); this is unchecked.

**Level workarounds:** `level-factory` is 8 near-identical "mint a level, define a function, return it
with its `level-of`" forms (WORKAROUNDS.md items 1–2), which one macro template would generate.

**Duplicates:** about 16 confirmed near-twins plus the ones noted per engine. None of the list-library
twins traces to the one-namespace issue (WORKAROUNDS.md item 5); each twin has its own name and the
earlier one was in scope. Patterns:
- **`dup-param`:** the same proof at a different parameter (node vs face, Und vs Abv, the three hypermap
  rotations, `fit.sl` at Sub vs Rg).
- **`dup-mirror`:** a symmetric argument written out again (`sq-down`/`sq-up`, `walk-x`, `seps-back`).
- **`dup-exact`:** `app-c` (unav/dbound.sl) is `lapp-c` (cfcolor.sl).

**Duplicated relations, not just lemmas:**
- `NCols` is a copy of `All2 NCol`.
- `CTr` is `TraceFrom` with `ColAdd` for `AddK`.
- `ColAdd` and `AddK` look like the same table.
- `NotIn`, `Distinct`, `HSub`, `Disj` and `Under` are all Nat-only Forall instances.

## 10. Language and library alternatives (owner questions)

Each of these would remove lemmas without a tactic. They are listed as questions; none is a recommendation
to change the code.

1. **Partial application of a type constructor as a relation argument.** This one was compiled, with the
   reference compiler on a scratch file.
   The check, loaded after `std/macro.sl`, `std/nat.sl` and `std/list.sl`:

```
(def-adts $ (All : (Type A) ((TyCtor (A x) -> Type) P) ((List A) xs) -> Type)
  enum
  (many AllNil : (erased Type A) (erased (TyCtor (A x) -> Type) P) -> (All A P (Nil A)))
  (many AllCons : (erased Type A) (erased (TyCtor (A x) -> Type) P) (erased A x) (erased (List A) xs) (erased (P x) p)
      (erased (All A P xs) rest) -> (All A P (Cons A x xs))))
(def-adts $ (UnderN : ((Nat) n) ((Nat) x) -> Type)
  enum
  (many MkUnderN : (erased (Nat) n x) (erased (Lt x n) p) -> (UnderN n x)))
(def-fns _ $ (erased t2 : (erased (Nat) n) (erased (List (Nat)) xs) (erased (All (Nat) (UnderN n) xs) a) -> (erased (All (Nat) (UnderN n) xs) r)) a)
```

   - **What compiles:** a generic `All (A) (P : TyCtor (A x) -> Type) xs` with `all-nth` and `all2-nth`
     lemmas, and `All (Nat) UnderAt xs` for a one-index `UnderAt`.
   - **What is rejected:** `All (Nat) (UnderN n) xs` for a two-index `UnderN`, with "`UnderN` expects 2
     arguments, got 1".
   - **Why it matters:** nearly every monomorphic Forall-like relation in the proof carries a context
     parameter (`Respects lab`, `Under n`, `HSub s`, `Orders p`). As things stand, those cannot be
     instances of the existing generic `All`/`All2`/`Pw`.
   - **What would fix it:** partial application or a type-level lambda for `TyCtor` arguments, or
     context-carrying generic types (`AllC C c P xs`, in the style `plan.sl`'s `AllR` and `red/kempe.sl`'s
     `Holds (MkPred ...)` already use).
   - **What it would remove:** pass 2 estimates 391 MAP lemmas (3,007 lines) recurse on or produce one of
     77 monomorphic All/All2-shaped relations; only 45 lemmas use the generic ones. Under either fix,
     about 180 rows (op-join/split, length, equiv) and about 80 Forall-elimination/conversion rows would
     become ~10 library lemmas.
   - **What would remain:** transport/convert/combine as library lemmas would still need the pointwise
     step passed as a function argument (WORKAROUNDS.md item 1), so they would stay macro-generated.
2. **Named field projection and named or nested record fields.** About 1,300–1,400 lines of adapters
   (`field-lift`, `rec-proj`, `bundle`), and the unpack lines inside most other categories.
3. **Mode polymorphism.** One definition serving both erased and `many` modes would merge the erased and
   runtime existence twins (E1b) and the three In deciders.
4. **One certificate carrier.** There are four interchangeable "maybe an erased proof of R" carriers:
   `ErasedMaybe` (76 uses), Bool+`IfT` (49), about 17 bespoke Yes/No ADTs, and the generic `Parse`, which
   already takes the relation as a parameter. One relation-parametric `Found` type (not compiled) would
   give every generator one output type and remove about a third of the lines in the partial checkers.
5. **Polymorphic membership and append.** `In` is Nat-only, `Elem` is polymorphic, `Adj` is `In` on
   bonds, and `Cat` is `LApp` at `Bond`. Merging them removes about 25 lemmas before any tactic exists.
6. **Arithmetic encodings.** Defining Thrice, Double and Trp via `Mul _ 3 _` / `Mul _ 2 _` would remove
   about half of `fnrel-conv`/`fnrel-mono`. One positional-numeral library would replace radix and
   bits-radix.
7. **Cyclic lists up to rotation**, for the rotation-transport family (feasibility not checked).
8. **Loading `std/tactics.sl`** in the four-colour unit. The proof proves Lt-chain lemmas by hand that
   `lt-lemma` appears to target.

## 11. How the engines depend on each other

Generation has an order, because each engine's hint table is largely the previous engines' output:

```
E1 FN (-fn)  ──► E1 fn-subst, E2 fa2-*/fa-post alignment, E3 FN refuters, E4 search
E1 EX (-exists, runtime -c) ──► E4 exists-close, E2 exists-map, E5 check+sound pairs
E1 NEG (excl, -fn clash) ──► E1 fn-guard refuters, E2 fa-multi, E4 cover-refute
E2a (R-length, R-snoc, R-app) ──► E2b transport of records containing R, rotations
E3 enum decide ──► E3 bits (per-bit step), E1 ex-fin/dec-fin
```

**Generated together:**
- per relation R: `-fn` with `-exists`, in both modes;
- per complementary pair: `dec` with `excl`;
- per closure ADT: `cat`/`snoc`/`intro`/`sym`;
- per list builder: the `thru-builder` kit;
- per conversion: `conv-iso` in both directions.

84 of the 165 uniqueness lemmas share a relation with an existence lemma.

## 12. Where it is concentrated

Lines by proof area. "Generic" counts pass-1 groups T1–T4 (roughly E1–E5), so the split is approximate:

| area | all lines | domain | generic (T1–T4) | glue/library | program | generic % |
|---|---|---|---|---|---|---|
| C-reducibility (`red/`) | 14,832 | 3,979 | 7,214 | 1,101 | 2,538 | 49% |
| unavoidability (`unav/`) | 6,483 | 1,157 | 4,306 | 641 | 379 | 66% |
| patch/snip/sew | 6,193 | 2,938 | 2,047 | 1,208 | 0 | 33% |
| configurations/colouring (`cf*`, `cp*`, `coloring`, `kempemap`) | 4,536 | 1,665 | 2,098 | 773 | 0 | 46% |
| hypermaps (`hyp*`) | 4,470 | 1,395 | 1,780 | 1,295 | 0 | 40% |
| other | 4,445 | 1,933 | 1,577 | 755 | 180 | 35% |
| Birkhoff (`birk*`, `minarity`, `contract*`) | 3,374 | 1,892 | 854 | 628 | 0 | 25% |
| Part A geometry | 2,946 | 1,378 | 1,084 | 480 | 4 | 37% |
| embedding (`embed*`, `notembed`) | 2,793 | 1,227 | 1,064 | 413 | 89 | 38% |

The certificate-checking halves (`unav/`, `red/`) are the most generic, because they are mostly
relations, their checkers and their soundness folds. The Birkhoff and patch arguments are the least.

## 13. Suggested prototype order

Pass 2's top picks, ranked by line count per unit of risk:

1. **E1a uniqueness (`fn-sd` + `fn-guard`).**
   - **Scope:** 136 lemmas, 1,147 lines, 880 of them H. It has one skeleton, needs a hint table plus five
     refuters, and its output is checked by type-checking.
   - **Regression targets:** `snoc-fn`, `revapp-fn`, `third-fn`, `bitwise-fn` (tuple hints), `hsum-fn`
     (Apart refuter), `esstep-fn` (clash refuter) and `cpmap-fn` (41 lines, a stress test).
   - **Then `fn-subst`:** its rewrite loop is this tactic's inner step.
2. **E2a list-builder kit (`op-join`/`op-split`/`length`, the `thru-builder` families).**
   - **Scope:** about 290 lemmas, 1,900 lines.
   - **Why early:** the two ADTs determine the proof, the existing generic `allr-*`/`pw-*`/`all2-*`
     lemmas give a ground truth to diff against, and it builds E2's core (lockstep inversion, rebuild,
     `values`).
3. **E2c Forall elimination (`fa-in`, `fa-nth`, then `fa2-*`).**
   - **Scope:** about 68 lemmas, nearly all H, needing no hints at the core.
   - **Do it alongside §10.1:** this is the clearest place to compare a tactic against the generic-type
     alternative directly.
4. **E3a enum `decide` (`enum-table`).**
   - **Scope:** 82 lemmas, 633 lines.
   - **Why it is low-risk:** it calls no lemmas, so levels cannot interfere, and it is generated from
     `def-adts` alone.
5. **E1b existence in both modes.** This starts with `ex-sd` and `rex-syntax`, emitted from the same
   mode annotations as (1). It then extends to the partial checkers once the carrier question (§10.4) is
   settled.
6. **E3b ring.sl extension.** Items 1–2 are auto-reification and linear combination. It has the biggest
   hand-written arithmetic payoff, but needs a design for passing hypotheses and certificates.
7. **E4 search engine.** It serves E2/E3 side goals as well as its own lemmas, but carries the most risk
   (argument synthesis).

Per CLAUDE.md rule 17, any of these that changes the elaborator would need slc-on-slc timing. A
macro-only prototype presumably does not.

## 14. Open questions

These are things this survey could not settle by reading; most can be settled by compiling something
small.

- **Can a macro inspect an ADT's constructors and field types,** or must a derive-style tactic take the raw
  `def-adts` form as input? (DESIGN.md §65 lists `resolve`, `settled-eq`, `settled-ty-apply` and
  `settled-val-apply`; none seems to enumerate constructors.)
- **Does matching `Refl` force the unification** that `fn-subst` relies on in every position it is used,
  and does `let-match` silently drop impossible lockstep constructor pairs as often as the code suggests?
  Several `-fn` lemmas list no cross cases at all.
- **How far does `_` inference reach** in hint calls, so that a generator need not synthesise every index
  argument?
- **Are literals and `Succ` chains canonicalised alike** for a type-directed hint lookup?
- **What does elaboration time cost** for large generated case trees (`enum-table`), measured against the
  hand-written ones?
- **Does splicing a lemma's name in macro output escape WORKAROUNDS.md item 1** in all cases, including
  erased lemmas used inside a level-factory function?
- **What is the `def-fns` `absurd` keyword** that appears on some refutation lemmas (`occ3-empty`)? Its
  effect was not checked.

## 15. Data files

`quasi-tactics-census.tsv`, next to this file, has one row per `def-fns` form. Its columns are:
- file and line (the form's first line);
- name, lines, and signature lines;
- engine and subcategory (as in this report's tables);
- confidence;
- pass-1 bucket;
- misbucket (the pass-2 note where a row was reassigned);
- relation.

Rows whose engine is `M misbucketed elsewhere (moved)` are excluded from the per-subcategory tables above.
The line numbers are those of the commit that adds this file, so they will drift as the proof changes.
