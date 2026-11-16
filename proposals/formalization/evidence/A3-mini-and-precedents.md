# A3: `mini/` as a starting point, and the precedents for large proofs in Sleight

Agent A3. Scratch directory: `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A3/`.
Nothing inside `/home/user/sleight` was modified by me.

## 0. Tags, and what I read

Every claim carries one of `[QUOTE file:line]`, `[RAN]`, `[READ file:lines]`, `[INFERENCE]`, or `[UNKNOWN]`.
A `[RAN]` that names a script means a script in my scratch directory; section 7 lists them with the commands.

What I read in full: the brief, the handoff, `CLAUDE.md`, `MINIMAL.md`, `mini/README.md`, all of `DESIGN.md`
(lines 1 to 3157), `mini/base.sl`, `term.sl`, `canon.sl`, `ctx.sl`, `unify.sl`, `core.sl`, `eval.sl`, `raw.sl`,
`elab.sl`, `preserve.sl`, `test/runtest.ml`, `stlc/README.md`, `higman/README.md`, `fourcolor/README.md`,
`fourcolor/WORKAROUNDS.md`.
What I read in part: `mini/elabfn.sl` lines 1-200, 318-417, 555-1345, and 1500-2388 (so every function of the
elaborator proper; NOT read: 201-317 and 418-554, small `sc-*` wrappers and list helpers, and 1346-1499, the
axiom checks and the `*Sc` evidence types; for those ranges I rely on `grep`, and say so where it matters).
For `stlc/` I read `types.sl`, `curry.sl`, `spec.sl`, `qed.sl`, `ispec.sl`, `iqed.sl`, `reducts.sl`, `proof.sl`,
`ctx.sl`, `skip.sl` lines 1-30, `jm.sl` lines 1-75, and the signatures of `subst.sl`. For the other precedents
I read the READMEs, the statement files, and the check scripts, not the proofs.

Everything in `mini/`, the READMEs, and the code comments was written by earlier sessions. Where I quote
them, that is what they say, not what the owner decided.

## 1. The findings that bear on decisions

1. **`mini/` works as shipped.** All ten `tests/mini_*.sl` print their expected line under the reference
   interpreter and under `slc`. `[RAN]` section 2.6.
2. **The top-level function has three outcomes, not two.** `elab-program` returns either an outcome with an
   erased derivation of `ElabProgram`, or `ProgramStuck`, which carries no evidence at all.
   `[READ mini/elabfn.sl:2373-2386]` So what the type checker has established is "accepted, rejected, or
   stuck", and the owner's "every program's source is either accepted or rejected" is not yet a theorem of
   `mini/`. I ran eleven inputs that come out stuck, among them the empty program, a program that ends in a
   statement, and a match branch with the wrong number of field names. `[RAN]` section 2.2.
3. **Nothing proves the two outcomes exclusive, or the stuck answer justified.** There is no lemma that a
   program has at most one outcome, and none that a stuck input has no derivation. `[READ]` the whole of
   `mini/` except the `elabfn.sl` ranges named above; `[RAN]` the grep of every function header in `mini/`
   (section 2.1) shows none whose name or type I read as either statement, and `preserve.sl` has five
   functions forming three lemmas. `[QUOTE mini/README.md:162-165]` "The metatheory MINIMAL.md anticipates (determinism of
   elaboration, totality of unification, confluence of canonicalization, evaluation of every well-typed
   program) is stated nowhere yet, nor is the agreement of an application's recorded former with its head's
   type (above)."
4. **Every stuck origin in the elaborator is a shape test on the raw syntax**, in 28 groups, one of which
   (pattern field count) also reads the context. `[READ mini/elabfn.sl:829-1122, 1613-2386]` Closing them
   looks additive: negative shape evidence plus an error rule per group. `[INFERENCE]` section 2.2.
5. **Only `eval` takes fuel**, and its fuel bounds the depth of the derivation. Canonicalization and
   unification recurse on erased measures with evidence, which costs nothing at run time. `[READ]` section 2.3.
6. **`Eval` is a pure big-step relation over environments and value trees.** No heap, no address, no
   mutation, no stripping of erased positions. `[READ mini/core.sl:6-43, mini/eval.sl:6-36]` If the spec's
   run is to be a mutating heap machine (handoff item 6, not confirmed by the owner), `core.sl` and `eval.sl`
   are replaced rather than extended; they are 258 of `mini/`'s 6,849 lines. `[RAN] wc -l mini/*.sl`
7. **The input is a hand-built `Sexp` with keywords already classified; there is no reader.**
   `[QUOTE mini/README.md:161]` "A reader from text to `Sexp` is not written; tests build `Sexp` by hand."
8. **Measured cost of the style.** The relations that the top-level statements are made of take 186 KB
   (179 ADTs, 662 rules). Everything that exists to derive them takes 421 KB: 86 KB of function-side evidence
   types, 203 KB of run-time functions, and 131 KB of erased lemmas. That is 2.3 bytes of deriving machinery
   per byte of relation. `[RAN]` section 2.7. In the eighteen judgments that have an error outcome, 110 of the
   168 rules are error rules. `[RAN]` section 2.7.
9. **`preserve.sl` holds three lemmas in 79 lines, and the preservation theorem it prepares for is written
   down nowhere.** `[READ mini/preserve.sl:1-79]`, `[RAN] grep -n -i preserv mini/README.md MINIMAL.md`
   (one hit, the file list entry).
10. **The gap to the full language is large and partly structural.** The DESIGN.md sections that `mini/`'s
    own comments cite come to about 640 of DESIGN.md's 3,157 lines. `[RAN]` section 2.8. Run-position
    evaluation, `comptime-match`, and macros make elaboration depend on evaluation (DESIGN.md §27, §29, §62),
    which changes the shape of the top-level theorem, not just the number of rules. `[INFERENCE]` section 2.8.
11. **Checking time is not the constraint.** Here, with the prebuilt `slc`: the 64,979-line four colour
    unit checks in 1 min 40 s, the BB(5) unit in 3 min 25 s, `stlc/` in under a second, and all of `mini/` in
    under 2 s. `[RAN]` section 3.
12. **There is agent cost data in the repository** for one certified program (solutions of 836 to 3,155
    lines): 25 of 28 runs passed; the three `claude-opus-5-5` runs each passed in their first session at 4.67 to 6.15 dollars.
    `[RAN]` section 3.7. The CSV was compiled by a Claude session and says of itself that its judgments "may
    be wrong".
13. **`stlc/` is the closest precedent and it is small**: 1,191 lines prove strong normalization of STLC in
    two formulations. Its reduction relation is small-step. Its method transfers; its de Bruijn code does
    not match `mini/`'s substitution design. `[READ]`, `[INFERENCE]` section 3.1.

**What these findings suggest for the proposals.** All `[INFERENCE]`; these are readings for the lead to
weigh, not recommendations the owner has seen.

- `mini/`'s checking side (everything but `core.sl` and `eval.sl`) is the reusable part. Its statement shape,
  a function that returns an outcome with a derivation, is already the "proved to agree with the spec" shape
  of the handoff's theorem targets, for a fragment and modulo the stuck answer.
- A bounded first job exists that would test the method on the owner's item 3: close the 28 stuck groups in
  `mini/` so that `ProgramDec` has no third constructor, and prove one outcome per program. Section 2.2 sizes
  the first half at 60 to 100 rules, or fewer with factored complements.
- Starting at source text needs a reader that `mini/` lacks. `self/reader.sl` is 742 lines of unverified
  Sleight (`[RAN] wc -l self/reader.sl`), and DESIGN.md has syntax that only the text carries: `[QUOTE DESIGN.md:156 §4]` "Pragmas are read from source text alone."
- For the full language, "malformed" cannot be separated from elaboration by a parser, because form
  recognition goes through head dispatch (§6). It has to be a family of rules in the relation.
- The run needs a decision before `eval.sl` is worth extending: its value trees cannot express slots or
  in-place writes (section 2.8).

## 2. Part 1: `mini/`

### 2.1 Inventory

Sizes. `[RAN] wc -l mini/*.sl; wc -c mini/*.sl`

| file | lines | bytes | content |
|---|---|---|---|
| `base.sl` | 138 | 8,119 | decided equality, list length and indexing with evidence |
| `term.sl` | 465 | 37,883 | `Term`, `Closed`, `Subst`, `Abstract`, `Assignable` |
| `canon.sl` | 312 | 26,291 | `Rule`, `Canon`, ranks |
| `ctx.sl` | 845 | 75,153 | context record, lookups, scoping invariants |
| `unify.sl` | 1,085 | 109,043 | `Unify`, the nested walk, `TypeOfTerm` |
| `core.sl` | 131 | 8,081 | `Core`, `Val`, `Env`, binding |
| `eval.sl` | 127 | 9,553 | `Eval` |
| `raw.sl` | 36 | 2,324 | test helpers |
| `elab.sl` | 1,243 | 144,748 | all elaboration relations, `Fails` |
| `elabfn.sl` | 2,388 | 210,960 | the deriving functions for `elab.sl` |
| `preserve.sl` | 79 | 6,093 | three lemmas |
| total | 6,849 | 638,248 | |

Counts. `[RAN] python3 -I adts.py mini/*.sl` (full listing saved as `proto/A3/adt-inventory.txt`): 355 ADTs
with 1,036 constructors, of which 318 are indexed (relations and evidence, 924 constructors) and 37 are plain
data (112 constructors). `[RAN]` a `grep -c` over function headers: 159 run-time (`many`) functions and 231
`erased` functions. I spot-checked the script's constructor counts for `ElabExpr` (39), `ElabTerm` (18),
`Unify` (24), and `Eval` (8) by counting the rules I read. `[READ mini/elab.sl:240-298, 616-769;
mini/unify.sl:153-233; mini/eval.sl:7-24]`

The principal judgments, their rules, and their deriving functions. Rule counts are from `adts.py`; the
function lines are from `[RAN] grep -n` over function headers; the pairing of relation to function is from my
reading of each function's return type. The DESIGN.md sections are the ones the files' own comments cite
(`[QUOTE]`s below the table), not a mapping the owner confirmed.

| relation (file:line) | rules | deriving function (file:line) | DESIGN.md §, per the comments |
|---|---|---|---|
| `Closed`/`ClosedList`/`ClosedTele` (term.sl:29) | 8/2/2 | none; evidence comes from `scoped-closed` (ctx.sl:252) and `assignable-closed` (term.sl:446) | 9 |
| `Subst`/`SubstList`/`SubstTele` (term.sl:59) | 9/2/2 | `subst`, `subst-list`, `subst-tele` (term.sl:96-148) | 9, 12 |
| `Somes`, `Snoc` (term.sl:152) | 2, 2 | `somes` (168), `snoc` (163) | |
| `IndexOf`, `NotIn` (term.sl:180) | 3, 3 | `index-dec` (198) | |
| `Abstract`/`AbstractList`/`AbstractTele` (term.sl:218) | 9/2/2 | `abstract*` (term.sl:252-293) | 9 |
| `Assignable*`, `Unassignable*`, `TeleDepth` (term.sl:301-368) | 8/2/2, 15/2/2, 2 | `assign-dec*` (term.sl:386-444) | 7 |
| `RuleOf`, `NoRule` (canon.sl:14) | 2, 2 | `rule-dec` (29), `rank-dec` (120) | 5, 7 |
| `Canon`/`CanonList`/`CanonTele` (canon.sl:38) | 9/2/2 | `canon*` (canon.sl:192-244), entered through `canon-tb` (unify.sl:599) | 7, 9 |
| `EntOf`/`NoEnt`, `NameOf`/`NoName`, `AdtOf`/`NoAdt` (ctx.sl:31-104) | 2 each | `ent-dec` (46), `name-dec` (74), `adt-dec` (106) | 5 |
| `LenEq` (base.sl:59), `LenMismatch` (ctx.sl:521) | 2, 3 | `len-dec` (ctx.sl:531) | |
| `Zip`/`ZipFail`, `ZipTele`/`ZipTeleFail` (unify.sl:21-47) | 2/3, 2/5 | `zip-dec` (57), `zip-tele-dec` (69) | 7 |
| `TypeOfTerm` (unify.sl:126) | 7 | `type-of-term` (unify.sl:624) | 10 |
| `Orient` (unify.sl:235) | 4 | `orient` (unify.sl:698) | 7 |
| `Unify` (unify.sl:153) | 24 | `unify-eqs` (unify.sl:1069), through the nested walk `unify-canon`, `ref-step`, `unify-list`, `unify-tele`, `after*` (828-1051), which derives `UnifyC` (23 rules, unify.sl:257), and the erased `conv*` (370-450), which turns `UnifyC` into `Unify` | 7, 9 |
| `EnvOf`, `BindAll`, `BindGroup`, `BindAtoms`, `BranchOf` (core.sl:46-117) | 2 each | `env-dec` (56), `bind-all` (75), `bind-group` (93), `bind-atoms` (106), `branch-dec` (123) | 24 |
| `Eval`/`EvalList`/`EvalStmt` (eval.sl:7) | 8/2/4 | `eval`, `eval-list`, `eval-stmt` (eval.sl:53-125), fuel | 27 |
| `Mint`, `Leave`, `Hide`, `Enter`, `AddAdt` (elab.sl:89-127) | 1 each | `mint` (elabfn.sl:34), `leave` (81), `hide` (89), `enter` (99), `add-adt` (108) | 27 |
| `Same`/`Differ`, `Refine`/`Contradict` (elab.sl:133-148) | 1 each | `same-dec` (elabfn.sl:587), `refine` (597) | 9, 7 |
| `TypeOf`, `KindOf`, `CanonAt`, `Typed` (elab.sl:152-164) | 1 each | `type-of` (562), `canonical` (571), `typed-dec` (616) | |
| `MintTele` (elab.sl:169) | 3 | `mint-tele` (elabfn.sl:629) | 12 |
| `ElabTerm` (elab.sl:240) | 18 | `elab-term`, `elab-term-app`, `elab-former`, `elab-fn`, `elab-valctor` (elabfn.sl:830-947) | 9, 11 |
| `ElabTermArgs` (elab.sl:345) | 8 | `elab-term-args` (elabfn.sl:948) | 12 |
| `ElabTele`, `EntryRaw`, `EntryMint` (elab.sl:374-406) | 6, 3, 2 | `elab-tele` (elabfn.sl:983), `entry-dec` (706) | 12 |
| `BadFormerRet` (elab.sl:301) | 4 | `former-ret-dec` (elabfn.sl:818) | 11 |
| `CallRaw`, `Plain`, `SubtermAt`, `NotAnnKey` (elab.sl:475-506) | 3, 6, 2, 10 | `call-raw-dec` (elabfn.sl:1110), `plain-dec` (1076), `subterm-at-dec` (1097), `ann-key-dec` (1069) | 19 |
| `StrictSub`, `SubOfList`, `NotSub`, `NotSubList` (elab.sl:524-545) | 2, 3, 2, 2 | `sub-dec`, `sub-list-dec` (elabfn.sl:673-696) | 18 |
| `Decrease` (elab.sl:867) with `MarkedIndex`, `SamePrefix`, `NotPredates`, `NotSubtermOf`, `Unmarked`, `DifferPrefix` | 15 | `decrease` (elabfn.sl:2083), `marked-index-dec` (1140), `prefix-dec` (1148), `predates-dec` (1191), `subterm-dec` (1213) | 19, 20 |
| `ElabExpr` (elab.sl:616) | 39 | `elab-expr` (elabfn.sl:1882), `elab-axiom-args` (1931), `elab-axiom` (1939), `elab-app` (1966), `elab-match` (2139), `elab-prove-subterm` (1831), `elab-prove-predates` (1849), `elab-former-expr` (1871) | 5, 7, 18, 21, 26, 27 |
| `AxiomBad` (elab.sl:776) | 12 | `axiom-check` (elabfn.sl:1400, not read) | 18 |
| `ElabItems` (elab.sl:820) | 5 | `elab-items` (elabfn.sl:2221) | |
| `ElabExprArgs` (elab.sl:833) | 9 | `elab-expr-args` (elabfn.sl:2035) | 14 |
| `CheckRets` (elab.sl:928) | 6 | `check-rets` (elabfn.sl:1586) | 26 |
| `ElabBranches` (elab.sl:945) | 9 | `elab-branches`, `elab-branch` (elabfn.sl:2170-2220) | 7, 21 |
| `Covered`, `Uncovered`, `Refuted`, `Reachable` (elab.sl:998-1019) | 3, 2, 1, 1 | `covered` (elabfn.sl:1675), `refuted` (1666) | 21 |
| `Unmatchable` (elab.sl:814) | 3 | `matchable-dec` (elabfn.sl:1317) | none; MINIMAL.md item 2 |
| `ElabBody` (elab.sl:1021) | 4 | `elab-body` (elabfn.sl:2238) | 27 |
| `ElabStmt` (elab.sl:1030) | 13 | `elab-stmt` (elabfn.sl:2258), `elab-let` (2280), `elab-def-fns` (2295), `elab-def-adts` (1817) | 27, 54 |
| `BindLet` (elab.sl:1071) | 9 | `bind-let` (elabfn.sl:1613) | 19, 27 |
| `MintFns`, `ElabBodies` (elab.sl:1104, 1127) | 5, 5 | `mint-fns`, `mint-fn` (elabfn.sl:1691-1726), `elab-bodies`, `elab-fn-body` (2314-2358) | 5 |
| `MintTycons`, `MintCtors`, `MintDeclCtors`, `BadRet` (elab.sl:1156-1217) | 4, 4, 6, 3 | `mint-tycons` (elabfn.sl:1769), `mint-ctors` (1789), `mint-decl-ctors`, `mint-decl-ctor` (1730-1768), `ret-dec` (1281) | 21 |
| `ElabProgram` (elab.sl:1229) | 3 | `elab-program` (elabfn.sl:2378) | 27 |
| `Fails` (elab.sl:1239) | 1 | the `PErr` outcome of `elab-program` | MINIMAL.md |

The files' own statements of what they formalize:

- `[QUOTE mini/term.sl:1-4]` "mini/term.sl -- the restricted type grammar of DESIGN.md section 9 as terms with
  de Bruijn telescopes (MINIMAL.md), and three relations over it with the functions that derive them:
  substitution of a telescope's binders, abstraction of scope entries into binders, and whether a term may be
  assigned to a variable (section 7's occurs check and its third contradiction)."
- `[QUOTE mini/canon.sl:1-2]` "mini/canon.sl -- the fact table's rewrite rules and canonicalization (DESIGN.md
  sections 5, 7 and 9) for the minimal language"
- `[QUOTE mini/ctx.sl:1-2]` "mini/ctx.sl -- the scope environment and fact table of DESIGN.md sections 5 and 7
  for the minimal language"
- `[QUOTE mini/unify.sl:1]` "mini/unify.sl -- forced unification (DESIGN.md section 7) for the minimal
  language, as a walk over a list"
- `[QUOTE mini/core.sl:2-3]` "Types are data (DESIGN.md section 24), so a type former in value position is a
  [CFormer] and evaluates to itself closed by the environment"
- `[QUOTE mini/eval.sl:2-3]` "An expression evaluates to as many values as its size (DESIGN.md section 27)"
- `[QUOTE mini/elab.sl:1-2]` "mini/elab.sl -- elaboration of the minimal language (MINIMAL.md) as relations:
  raw syntax to core code (mini/core.sl) with the types and facts of DESIGN.md sections 5 to 7, 9, 18 to 21,
  26 and 27."

Three things I checked against DESIGN.md's text:

- `Term`'s constructors follow §9's four productions with §10's `Univ`. `[READ mini/term.sl:11-24]` against
  `[QUOTE DESIGN.md:421-427 §9]` "A type is built from: 1. variable references, 2. applications of a type
  constructor, 3. applications of a value constructor, 4. applications of a type former: `Fn`, `UniqueFn`,
  `TyCtor`, `ValCtor` (§11), `Matchable` (§24) or `Cell` (§37)." `mini/` has `Ref`/`Bound`, `TyApp`, `ValApp`,
  `TFn`, `TTyCtor`, `TValCtor`, and `TUniv`; it has no `UniqueFn`, `Matchable`, or `Cell` former.
- **A count disagrees.** `[QUOTE MINIMAL.md:58-59]` "the scope table and fact table with branch-forced
  unification and its three contradictions (sections 5, 7)" and `[QUOTE mini/unify.sl:5-6]` "The three
  contradictions are the [UFail] rules: an unassignable term (the occurs check and a telescope binder), two
  rigid atoms, and two shapes that differ." DESIGN.md now says `[QUOTE DESIGN.md:310 §7]` "Forcing fails, and
  so refutes the branch, in exactly four cases:". `mini/` groups §7's cases 1 and 3 as one, so the behaviours
  may still line up; I did not check each case of §7 against `Unify`'s rules. `[UNKNOWN]`
- **`mini/`'s rigidity rule is not the full language's.** `mini/` refuses two distinct declared atoms
  (`URigidRigid`, `[READ mini/unify.sl:231-233]`), by MINIMAL.md item 2. The full language says
  `[QUOTE DESIGN.md:317-319 §7]` "A declared name has no distinctness of its own: two type constructors with
  identical signatures and no opened `Matchable` unify."

### 2.2 The top-level statements, and every stuck path

The relations, exactly. `[QUOTE mini/elab.sl:1225-1241]`

```
  ((POut : -> Type)
    enum
    (many POk : (many (Core) core) (many (Term) ty) -> (POut))
    (many PErr : (many (Reason) r) -> (POut)))
  ((ElabProgram : ((List (Sexp)) items) ((POut) out) -> Type)
    enum
    (many ProgramOk : (erased (List (Sexp)) items) (erased (Ctx) ctx) (erased (Core) core) (erased (Nat) x) (erased (Term) ty)
       (erased (ElabBody init-ctx items (EOk ctx core (Cons (Nat) x (Nil (Nat))))) p) (erased (TypeOf ctx x ty) t) -> (ElabProgram items (POk core ty)))
    (many ProgramSize : (erased (List (Sexp)) items) (erased (Ctx) ctx) (erased (Core) core) (erased (List (Nat)) ids) (erased (ElabBody init-ctx items (EOk ctx core ids)) p) (erased (NotOne ids) n)
       -> (ElabProgram items (PErr (RSize))))
    (many ProgramErr : (erased (List (Sexp)) items) (erased (Reason) r) (erased (ElabBody init-ctx items (EErr r)) p) -> (ElabProgram items (PErr r)))))
```
```
  ((Fails : ((List (Sexp)) items) ((Reason) r) -> Type)
    enum
    (many FailsBy : (erased (List (Sexp)) items) (erased (Reason) r) (erased (ElabProgram items (PErr r)) p) -> (Fails items r))))
```

So `ElabProgram items out` relates a list of raw forms to one outcome: `POk core ty`, the core code and the
type of the program's one value, or `PErr r`, one of 15 `Reason`s (`[READ mini/elab.sl:43-59]`).
`Fails items r` is a wrapper around the `PErr` case. Typing and failing are one relation by design:
`[QUOTE mini/elab.sl:3-4]` "Each judgment is total, its outcome an [Ok] with what was derived or an [Err] with
the first reason found, so that the relation that types a program and the [Fails] relation are one."

The function, exactly. `[QUOTE mini/elabfn.sl:2373-2378]`

```
(def-adts
  ((ProgramDec : ((List (Sexp)) items) -> Type)
    enum
    (many MkProgramDec : (erased (List (Sexp)) items) (many (POut) out) (erased (ElabProgram items out) p) -> (ProgramDec items))
    (many ProgramStuck : (erased (List (Sexp)) items) -> (ProgramDec items))))
(def-fns _ $ (many elab-program : (many (List (Sexp)) items) -> (many (ProgramDec items) r))
```

What that type establishes, given that it type-checks: for every `items`, `elab-program` returns an outcome
together with a derivation that `items` has that outcome, or returns `ProgramStuck`. `[INFERENCE]` from the
type; it rests on the checker being right. It establishes nothing about `ProgramStuck` inputs, and nothing
about a program having only one outcome.

The comment "Each judgment is total" and the stuck answer are reconciled by the authors this way:
`[QUOTE mini/elab.sl:40-42]` "Why a program is refused: the first reason met, carried out unchanged by every
enclosing judgment. A malformed shape is not a reason: the relations have no derivation for one, and [Fails]
speaks of well-formed programs that do not type." and `[QUOTE mini/README.md:140-143]` "**Malformed syntax
has no derivation.** `Fails` records why a well-formed program is refused; a shape the rules do not recognize
derives nothing, and the functions answer "stuck" on it. A branch pattern with the wrong number of field
names counts as such a shape."

**The stuck constructors.** `[RAN] grep -c "Stuck"` over `mini/` (216 hits in the `.sl` files, one in the README). Declarations: in `elabfn.sl`,
`AtomNamesStuck` (363), `TermStuck` (747), `ArgsStuck` (752), `TeleStuck` (757), `CallRawStuck` (1057),
`ExprStuck` (1516), `ItemsStuck` (1520), `ExprArgsStuck` (1525), `DecreaseStuck` (1530), `BranchesStuck`
(1535), `BodyStuck` (1547), `StmtStuck` (1551), `BindLetStuck` (1556), `FnsStuck` (1560), `BodiesStuck`
(1564), `TyconsStuck` (1568), `CtorsStuck` (1572), `DeclCtorsStuck` (1576), `ProgramStuck` (2377); in
`eval.sl`, `EvalStuck` (42), `EvalListStuck` (46), `EvalStmtStuck` (50); in `core.sl`, `BDStuck` (73). Five
more answers are negative with no evidence and feed a stuck: `EntryNot` (elabfn.sl:705), `PlainNo` (1037),
`SubAtNo` (1053) in the elaborator, and `EnvMiss` (core.sl:54) and `BrMiss` (core.sl:121) in the evaluator.
None of these constructors carries a proof.

**Where the elaborator originates a stuck** (every other occurrence passes one up from a callee).
`[READ mini/elabfn.sl:829-1122, 1613-2386]` Line numbers are `elabfn.sl`'s.

| # | where | the shape that is stuck | what closing it would take `[INFERENCE]` |
|---|---|---|---|
| T1 | 839 | a bare keyword where a term is expected | one rule; the conclusion's own index `(RKey k)` is the shape, so no evidence is needed |
| T2 | 841 | the empty list `()` where a term is expected | one rule, likewise |
| T3 | 882-889 | `(Fn ...)` not exactly `(Fn L (params) (rets))` | rules for too few items, too many, params not a list, rets not a list; needs a "not a list" relation (two constructors) |
| T4 | 891-893 | `(TyCtor ...)` not exactly `(TyCtor (params))` | as T3, fewer cases |
| T5 | 901-906 | `(ValCtor ...)` not exactly `(ValCtor (params) ret)` | as T3 |
| T6 | 907 | a list headed by any other keyword where a term is expected, such as a `match` or a `values` in a type | one rule and a complement of `FormerKey` over the 17 keys (14 constructors), as `NotAnnKey` already is for the annotation keys |
| T7 | 987, with 706-727 | a telescope entry that is not `(T x)`, `(subterm T x)`, or `(e is x)` | a complement of `EntryRaw`; `entry-dec` has nine evidence-free exits, so about nine constructors; shared with S6 |
| E1 | 1890 | a bare keyword where an expression is expected | one rule, as T1 |
| E2 | 1892 | the empty list where an expression is expected | one rule |
| E3 | 1907-1911 | `(match ...)` without a scrutinee and an annotation list | about three rules |
| E4 | 1913-1917 | `(prove-subterm ...)` without exactly two items | about three rules, or one with a length-mismatch premise |
| E5 | 1919-1925 | `(prove-predates ...)` without exactly two atoms | about four rules; needs "not an atom" |
| E6 | 1933-1937 | an axiom form without exactly two items | as E4 |
| E7 | 1929 | a list headed by `let`, `def-lvl`, `def-fns`, `def-adts`, `is`, `subterm`, or `predates` where an expression is expected; this includes a body or a program that ends in a statement, and a decrease annotation among a constructor's arguments | one rule and a seven-constructor key relation; or, for a body that ends in a statement, a decision to give it §27's meaning instead |
| E8 | 1116, 1121, reached from 2008 | a call whose annotation is misplaced, doubled, or malformed | the largest: complements of `Plain` and `SubtermAt` (`plain-dec` and `subterm-at-dec` answer `PlainNo` and `SubAtNo` with no evidence) |
| B1 | 2174-2180 | a match branch that is not `((C fields...) items...)` | about four rules |
| B2 | 2194, with 364-369 | a branch field name that is not an atom | a two-constructor complement of `AtomNames` and one rule |
| B3 | 2195 | a branch pattern whose number of field names differs from the constructor's number of fields; this reads the context | one rule; the `LenMismatch` evidence already exists and is discarded |
| B4 | 2239 | an empty body: the empty program, a function with no body items, a branch with no body, a `let` with no right-hand side | one rule in `ElabBody` |
| S1 | 2259-2261, 2279 | a non-final body item that is not a list headed by `let`, `def-lvl`, `def-fns`, or `def-adts`, such as an expression in statement position | about five rules and a thirteen-constructor key relation |
| S2 | 2264-2267 | `(let ...)` without a binder list | about two rules |
| S3 | 2269-2271 | `(def-lvl ...)` without exactly one atom | about three rules |
| S4 | 2275-2277 | `(def-fns)` with no level | one rule |
| S5 | 1694-1702 and 2322-2330 | a `def-fns` definition that is not `(f (params) (rets) items...)` | first site: about six rules. Second site: a **refutation**, not a rule; `elab-bodies` walks definitions that `mint-fns` already accepted, so carrying the `MintFns` derivation and inverting it would rule the shape out |
| S6 | 1633 | a `let` binder that is neither an atom nor an entry shape | the complement of `EntryRaw` from T7 |
| S7 | 1634 | a `let` binder marked `subterm` | one rule; the shape is positive |
| S8 | 1772-1776 and 1795-1799 | a `def-adts` declaration that is not `(T (params) ctors...)` | first site: about five rules. Second site: a **refutation** from the `MintTycons` derivation, as in S5 |
| S9 | 1733-1741 | a constructor declaration that is not `(C (fields) ret)` | about six rules |

Summed, that is on the order of 60 to 100 new rules if each complement is written out by pattern, or about ten
small complement relations and 30 rules if "not a list", "not an atom", "wrong length", and the key
complements are factored out; two sites call for a refutation instead. `[INFERENCE]`; counted from the exits
of the deciders as read, not built.

`[RAN]` I built eleven such programs and three controls and ran `elab-program` on each, with the reference
and with `slc --interpret`; both printed the same line. Command:
`main.exe mini/{base,term,canon,ctx,unify,core,eval,elab,elabfn,raw}.sl proto/A3/stuck_demo.sl`. Output, where
`(None _)` is `ProgramStuck`, `(Some _ $ None _)` is accepted, and `(Some _ $ Some _ $ r)` is refused with `r`:

```
(Cons _ (Some _ $ None _) $ Cons _ (Some _ $ Some _ $ RNotInScope) $ Cons _ (None _) $ Cons _ (None _) $ Cons _ (None _) $ Cons _ (None _) $ Cons _ (None _) $ Cons _ (None _) $ Cons _ (None _) $ Cons _ (Some _ $ Some _ $ RBadProof) $ Cons _ (None _) $ Cons _ (None _) $ Cons _ (None _) $ Cons _ (None _) $ Nil _)
```

In order: control accepted; control refused; stuck on the empty program (B4); on `((Succ) (Zero))` as a
branch of a match on a `Nat` (B3, too few names); on `((Zero z) (Zero))` (B3, too many); on a program that is
only a `def-adts` (E7); on `(Zero) (Zero)` as a program (S1); on `(Succ (predates p))` (E7); on
`(f (predates p) (subterm q) (Zero))` (E8); control `(f (predates p) (Zero))` at the top level refused with
`RBadProof`; stuck on `(let (((values) x)) (Zero))` (T6); on a bare `values` keyword as the final expression
(E1); on `(def-lvl L M)` (S3); on `(let ((subterm (Nat) x)) (Zero))` (S7).

Notes on the list:

- B3 is not syntax alone, and the evidence it needs already exists: `len-dec` returns a `LenMismatch` proof
  and line 2195 discards it. `[READ mini/elabfn.sl:2195, mini/ctx.sl:521-537]`
- E7 makes "a program that ends in a statement" stuck, where DESIGN.md gives it a meaning:
  `[QUOTE DESIGN.md:1163-1164 §27]` "A file that ends in a statement produces nothing."
- A semantic stuck existed once and was removed by a rule change. `[QUOTE tests/mini_untyped_rule.sl:4-6]`
  "While the former accepted any type as its return, this program reached [type-of-term]'s stuck, so that (in
  one session's reading) no derivation of [ElabProgram] existed for it". Today `type-of-term`'s result type
  has one constructor, `TotIs`, so that path cannot answer stuck. `[READ mini/unify.sl:621-641]` The header
  of `elabfn.sl` still says otherwise and is stale: `[QUOTE mini/elabfn.sl:4-5]` "a stuck answer is a
  malformed shape the relations have no rule for, with the one exception noted at [type-of-term]".
- `raw.sl`'s `outcome` helper reports `ProgramStuck` as `RSize`, so tests that use it cannot tell the two
  apart. `[READ mini/raw.sl:30-34]`

**What each would take.** All `[INFERENCE]`, resting on the reading above; none of it was built.

1. *Add rules, keep `Sexp`.* The table's last column sizes this per group: an error rule that concludes,
   say, `Err RMalformed`, and where the shape is a complement, evidence for it. B3 and the groups whose shape
   is positive (T1, T2, E1, E2, B4, S4, S7) need a rule and no new evidence type. The others need evidence the
   deciders do not produce today (`EntryNot`, `PlainNo`, `SubAtNo`, and every `else` in the table are
   evidence-free). `mini/` shows what hand-written complements cost: `NotApp`, `NotTyApp`, `NotTyCtor`,
   `NoTele`, `NoTeleNoFn`, and `NonRef` are six near-identical "not this shape" relations with 2 to 7
   constructors each (`[READ mini/elab.sl:223-234, 308-330, 806-812; mini/unify.sl:97-105]`). The shapes in
   the table are nested three or four deep, so per-form complements would be larger than those.
2. *One generic matcher.* Define a small pattern language over `Sexp` (atom, given keyword, list of
   patterns, rest), one relation "matches", and one complement, proved once. Each judgment's malformed rule
   then cites the complement for its own patterns. This puts the cost in one place instead of 28.
3. *Parse to a typed syntax first.* A parser from `Sexp` to an ADT that has only well-formed shapes would
   remove every stuck from the judgments. It fits MINIMAL.md's fragment, where keywords are reserved. It does
   not fit the full language, where what a list is depends on the value of its head: `[QUOTE DESIGN.md:234-239
   §6]` "A list is elaborated according to its head: 1. The head is elaborated first. If its result is a
   `Settled`, non-erased entry whose minted type canonicalizes to `(Special)` against the facts of the
   innermost enclosing run position (§27), the list is the special form named by that entry's stored value."
   and `[QUOTE DESIGN.md:741-743 §19]` "**One namespace.** Special forms, types and values share one
   namespace. Everything in it may be shadowed, including special forms and types." So for the full language
   the malformed-form rules have to be rules of the elaboration relation itself.
4. *Refute instead.* Proving that a stuck input has no derivation would give "accepted, rejected, or
   provably neither", which is still three outcomes, so it does not by itself meet the owner's statement.

**Where the evaluator originates a stuck.** `[READ mini/eval.sl:52-125, mini/core.sl:56-81, 123-129]`

| where | cause |
|---|---|
| eval.sl:54, 103, 112 | fuel is `Zero` |
| eval.sl:58 | variable not in the environment (`EnvMiss`) |
| eval.sl:62-64 | an application's head is not exactly one value, or not a `VAtom` |
| eval.sl:70-72 | a call's head is not exactly one value, or not a `VClo` |
| eval.sl:83-85 | a scrutinee is not exactly one value, or not a `VCon` |
| eval.sl:86 | no branch for the scrutinee's constructor (`BrMiss`) |
| eval.sl:76, 87, 116-117, with core.sl:77-80 | ids and values differ in number (`BDStuck`) |
| eval.sl:106-107 | a list item is not exactly one value |

Fuel exhaustion and a run-time shape error are the same answer, `EvalStuck`, with no evidence. `[RAN]` the
program of `tests/mini_elab.sl` under `(eval n init-env core)` (`proto/A3/fuel_demo.sl`) answers stuck for
n = 5, 8, 9, and 10 and its value for n = 500. Turning the shape errors into refutations needs a typing
judgment for `Val` and `Env`, which `mini/` does not have (`[RAN] grep -l "(Val)\|(Env)" mini/*.sl` names only `core.sl`, `eval.sl`, and
`raw.sl`, and `[READ]` of those shows the relations over them are `EnvOf`, `BindAll`, `BindGroup`,
`BindAtoms`, and `Eval*`, with their decision results), plus a proof that elaborated code keeps it. `[INFERENCE]` Removing the fuel needs either a termination proof from the level and subterm
checks, or a step machine driven from outside, which is the handoff's item 2.

### 2.3 Fuel

- **Only `eval` takes fuel.** `[RAN] grep -n -i fuel mini/*.sl mini/README.md MINIMAL.md` finds the word only
  in `eval.sl` (lines 53, 54, 102, 103, 111, 112), a comment in `term.sl:5`, and the README. The three
  functions each take `(subterm many (Nat) fuel)` and answer stuck at `Zero`. `[READ mini/eval.sl:53-54,
  102-103, 111-112]` `raw.sl`'s `run` passes 500. `[READ mini/raw.sl:25]`
- **The fuel bounds depth, not steps.** Every recursive call in a body passes the same predecessor `f`,
  including the calls on sibling arguments. `[READ mini/eval.sl:61, 65, 69, 74, 77, 105, 108]`
- **The other `subterm ... (Nat)` parameters are not fuel.** `[RAN] grep -n "subterm many (Nat)\|subterm
  erased (Nat)" mini/*.sl` lists, besides `eval`: `canon*` and the unification walk with an *erased* `n`,
  `prefix-dec`'s `j` (elabfn.sl:1148, the number of leading arguments to compare, a real input), and
  `plus-zero` (base.sl:92, a lemma). An erased parameter cannot be inspected at run time, so it cannot make a
  function give up; it only orders the recursion. `[INFERENCE]` from DESIGN.md §14's erasure rules.
- **Canonicalization: recursion on a rank bound, then the term.** `[READ mini/canon.sl:67-118, 191-244]`
  Each rule has a rank. `ValidFrom rules ranks rules ranks` says every rule's term is `Below` its own rank,
  and `Below rules ranks t k` says every ruled entry `t` mentions has rank under `k`. `canon` takes
  `(subterm erased (Nat) n) (subterm many (Term) t) (erased (Below rules ranks t n) b)`. At an entry with a
  rule it recurses on the rule's term under the rule's own rank, which `Below` proves smaller:
  `[QUOTE mini/canon.sl:201]` "(let ((many u) (erased q)) (tail $ canon rules ranks v (subterm (lt-subterm k
  n lt)) k r (valid-below rules ranks rules ranks x r k v p)))". Everywhere else it recurses on a subterm
  under the same bound. The starting bound is a `top` above every rank, kept with the rules.
  `[READ mini/unify.sl:599-600]`
- **How the ranks stay valid.** A rule minted with a fresh entry takes rank `top`, and `top` grows by one.
  `[READ mini/elabfn.sl:45-56, mini/ctx.sl:799-802]` A rule minted by unification takes rank zero and every
  other rank grows by one; that is sound because the new rule's term is canonical and passed the occurs
  check, so it mentions no ruled entry. `[READ mini/unify.sl:500-501, 517-596]`
- **Unification: recursion on the count of rule-free entries, then the left term, then a phase.**
  `[READ mini/unify.sl:452-498, 828-831]` `FreeCount ents rules n` counts the entries with no rule;
  `assign-count` shows that minting a rule for one of them gives a count `m` with `Lt m n`. `unify-canon`
  takes `(subterm erased (Nat) n) (erased (FreeCount ents rules n) fc) (subterm many (Term) l) ... (subterm
  many (POuter (PInner)) is phase)`. After a mint the walk re-canonicalizes what is left and continues under
  the smaller count. `[READ mini/unify.sl:850, 956, 1021, 1036, 1050]`
- **Elaboration: recursion on the raw syntax, then a phase, then a list tail.** `[QUOTE mini/elabfn.sl:1879-
  1880]` "The group proper. Each function decreases on the raw syntax it walks, then on a phase for a call
  that walks the same syntax, then on the list of arguments still to be walked." `[READ mini/elabfn.sl:1882,
  1966, 2035-2036]` confirms the signatures.

### 2.4 Input and output

- **Input.** `elab-program` takes `(List (Sexp))`. `Sexp` is `RAtom String`, `RKey Key`, or `RList (List
  Sexp)`, and `Key` has 17 keywords. `[READ mini/elab.sl:14-38]` Keywords arrive already classified:
  `[QUOTE mini/elab.sl:8-9]` "The reader turns keyword atoms into [RKey], so keywords are reserved and a name
  never is one." No such reader exists (`[QUOTE mini/README.md:161]`, above). The tests build `Sexp` with
  `raw.sl`'s helpers `a`, `k`, and `l0` to `l5`. `[READ mini/raw.sl:4-17, tests/mini_elab.sl:12-15]` The
  surface syntax itself is that session's: `[QUOTE MINIMAL.md:109-112]` "The surface syntax of the minimal
  language, chosen by the session that wrote `mini/` because the full language's telescopes and binders are
  told apart by their multiplicity tokens, which the minimal language lacks."
- **Output.** On success, a `Core` and a `Term` (the type). `Core` is `CVar`, `CApp`, `CCall`, `CMatch`,
  `CValues`, `CFormer`, `CToken`, or `CStmt`; a `Stmt` is `SLet`, `SDefLvl`, `SDefFns`, or `SDefAdts`.
  `[READ mini/core.sl:6-28]`
- **`Eval` is big-step, over pure values and environments.** `Eval : ((Env) env) ((Core) c) ((List (Val))
  vs) -> Type`. `[READ mini/eval.sl:7]` A `Val` is `VCon head args`, `VAtom id`, `VFormer term env`,
  `VClo env group def`, or `VToken`; an `Env` is `ENil` or `ECons id v rest`. `[READ mini/core.sl:32-43]`
  There is no heap, store, address, slot, cell, or world anywhere in `mini/`: `[RAN] grep -n -i -w
  "heap\|address\|addr\|slot\|slots\|cell\|store\|mutat[a-z]*\|unique\|world" mini/*.sl mini/README.md` finds
  only lemma names such as `rule-rank-unique`. The eight rules bind and look up; none writes.
  `[READ mini/eval.sl:9-24]`
- **Types are run-time data, and proofs are a unit token.** A former evaluates to itself closed over the
  environment (`EvFormer`), and every level and proof is `CToken`, evaluating to `VToken`.
  `[READ mini/eval.sl:21-22, 34]` There is no erasure, so nothing is stripped before evaluation.
- **Elaboration never evaluates.** A top-level call elaborates like any call, minting fresh entries for its
  results; it is not run. `[READ mini/elab.sl:651-657, 869]` `raw.sl`'s `run` elaborates, then evaluates.
  `[READ mini/raw.sl:22-27]` This is MINIMAL.md's cut: `[QUOTE MINIMAL.md:31-33]` "Elaboration is a pure
  function from raw syntax to core terms; evaluation is a separate phase after it."

### 2.5 `preserve.sl`

What is proved. `[READ mini/preserve.sl:1-79]`

1. `rule-of-unique`: two `RuleOf rules x _` derivations give equal terms.
2. `canon-unique`, with its list and telescope forms: `Canon rules t u` and `Canon rules t u2` give
   `Eq (Term) u u2`. Canonicalization is a function of the rules.
3. `elab-term-typed`: `ElabTerm ctx raw (TOk t ty)` gives `Typed ctx t ty`.

`[RAN]` `tests/mini_preserve.sl` loads the file; its expected line is `(BTrue)`, so the test checks only that
the three lemmas type-check.

What the README says is open. `[QUOTE mini/README.md:43-45]` "`preserve.sl` — groundwork for the open
preservation argument below: canonicalization is a function of the rules, and `ElabTerm` forms only what
`TypeOfTerm` types. Not needed by the elaborator." The "below" has no referent that states the argument: the
README's "Open" section holds the reader item and the metatheory item quoted in finding 3, and neither states
a preservation theorem. `[READ mini/README.md:159-165]` What exactly is to be preserved is `[UNKNOWN]`.
One further debt is named: `[QUOTE mini/README.md:92-95]` "Not checked anywhere, and so owed to the
metatheory in the session's reading: that under the rules in force the recorded former agrees with the head's
canonical type, without which `TypeOfTerm` types a `ValApp` by a return its head does not have."

What the next lemmas would have to be. All `[INFERENCE]`; it rests on the relations as I read them and on
the usual shape of such arguments, and could be checked only by attempting them.

1. Determinism of the remaining relations: `Subst`, `Abstract`, `Unify` (one outcome and one resulting rule
   list per input), then each `Elab*` judgment. This is what "never both accepted and rejected" needs.
2. The recorded-former agreement the README names.
3. A typing relation for `Val` against `Term`, and an agreement relation between an `Env` and a `Ctx`: each
   entry has a value of its type, and each rule holds of the values. Neither exists.
4. Typing kept under `Grew` (the scoping analogues exist: `scoped-ext`, `sc-grew`), and under `Subst`
   (the scoping analogue exists: `subst-scoped`). `[READ mini/ctx.sl:318-359, 658-661; mini/elabfn.sl:119-122]`
5. Soundness of `Refine`: if the scrutinee's value is headed by the branch's constructor, the environment
   extended with the fields satisfies the minted rules. And soundness of `Contradict`: a refuted constructor
   never heads the scrutinee's value. With `Covered`, that is what makes `EvMatch`'s branch lookup succeed.
6. `ElabExpr` typed: the core it emits evaluates, when it evaluates, to values of the types of the ids it
   returns. This is the preservation statement proper.
7. Termination from `Decrease`: every accepted program has an `Eval` derivation. This is the lemma that
   would remove the fuel. MINIMAL.md names it: `[QUOTE MINIMAL.md:113-115]` "The metatheory to state:
   determinism of elaboration, totality of unification, confluence of canonicalization, and every well-typed
   program evaluating, section 10's claim."

### 2.6 Running the tests

How the runner turns `; needs:` into a run. `[QUOTE test/runtest.ml:3]` "\"; needs: a b\" runs tests/a.sl and
tests/b.sl first in the same scope;". The names are split on spaces and each is read as `tests/<name>.sl`, so
`../mini/base` is `tests/../mini/base.sl`. `[READ test/runtest.ml:95, 134-142]` The runner clears what the
needed files printed before it runs the test, so only the test's own final line is compared.
`[READ test/runtest.ml:145, 174, 187]` `self/bootstrap.sh` does the same on a command line:
`[QUOTE self/bootstrap.sh:51]` "for n in $(directive \"$t\" needs); do needs=\"$needs tests/$n.sl\"; done",
then runs the reference as `$REF $both $confine $files`, `slc` as `slc $both $confine --interpret $files`, and
`slc $both $confine $flags --byte --build "$B/$name.exe" $files`, with `--warn-unused` in `$both`.
`[READ self/bootstrap.sh:56-58, 101, 109, 114]` `[QUOTE MANUAL.md:284]` "`; needs: list vec` runs those files
first in the same scope,".

By hand, for example:
`_build/default/bin/main.exe tests/../mini/base.sl tests/../mini/term.sl tests/mini_term.sl`.

`[RAN] proto/A3/run_mini_ref.sh` (reference, three runs: no flags, `--warn-unused`, `--no-extern`),
`proto/A3/run_mini_slc.sh interpret`, and `proto/A3/run_mini_slc.sh build`. Each test's last printed line
equalled its `; expect:` line in every run, every exit code was 0, and stderr was empty. Wall-clock seconds,
4-core VM, load average at or under 1 when these ran:

| test | reference, runs 1/2/3 | `slc --interpret` | `slc --byte --build` | built program |
|---|---|---|---|---|
| `mini_axioms` | 3.19 / 3.37 / 3.22 | 1.99 | 2.10 | 0.01 |
| `mini_dependent` | 3.35 / 3.27 / 3.24 | 1.98 | 2.25 | 0.01 |
| `mini_elab` | 3.28 / 3.16 / 3.26 | 1.94 | 2.16 | 0.01 |
| `mini_eval` | 0.61 / 0.56 / 0.55 | 0.37 | 0.61 | 0.01 |
| `mini_fails` | 3.30 / 3.57 / 3.22 | 1.93 | 2.27 | 0.01 |
| `mini_preserve` | 1.68 / 1.94 / 1.62 | 1.19 | 1.25 | 0.01 |
| `mini_recursion` | 3.50 / 3.36 / 3.14 | 1.93 | 2.16 | 0.01 |
| `mini_term` | 0.55 / 0.56 / 0.54 | 0.42 | 0.54 | 0.01 |
| `mini_unify` | 1.32 / 1.38 / 1.43 | 0.85 | 1.02 | 0.01 |
| `mini_untyped_rule` | 3.39 / 3.18 / 3.23 | 2.08 | 2.09 | 0.01 |

So `slc` handles all ten, in both modes. The built programs take 0.01 s because each test's final value is
computed when the file is elaborated and the program only prints it. `[INFERENCE]` from the timing and from
`[QUOTE self/README.md:51-52]` "the values it computes are embedded in the OCaml output as data, closures
included, rather than recomputed".

Where the time goes. `[RAN] proto/A3/cumulative.sh`: loading the files cumulatively, each ending in
`(MkUnit)`.

| through | cumulative lines | reference | `slc --interpret` |
|---|---|---|---|
| prelude only | 1 | 0.43 s | 0.28 s |
| `base` | 138 | 0.42 | 0.34 |
| `term` | 603 | 0.52 | 0.37 |
| `canon` | 915 | 0.60 | 0.42 |
| `ctx` | 1,760 | 0.80 | 0.58 |
| `unify` | 2,845 | 1.20 | 0.80 |
| `core` | 2,976 | 1.31 | 0.86 |
| `eval` | 3,103 | 1.33 | 0.86 |
| `elab` | 4,346 | 1.85 | 1.14 |
| `elabfn` | 6,734 | 3.45 | 1.93 |
| `raw` | 6,770 | 3.35 | 1.88 |

Net of the prelude, all of `mini/` checks in about 3.0 s with the reference and 1.6 s with `slc`.

### 2.7 What the style costs

Two representative rules. Sizes are `[RAN]` with `sed -n 'a,bp' file | wc -c` over the ranges given.

*Simple: a name as an expression.* The relation's two rules, `EXName` and `EXUnbound`, are 3 lines at
`elab.sl:619-621`; `EXName` alone is 2 lines, 246 bytes, with 6 erased parameters. The function's case for
both rules is 6 lines, 467 bytes, at `elabfn.sl:1884-1889`. `[READ]` both.

*Complex: a call.* `EXCall` is 7 lines, 1,116 bytes, with 32 erased entries (21 variables and 11 premises),
at `elab.sl:651-657`. Its two error rules, `EXCallArgsErr` and `EXCallDecreaseErr`, repeat its premises up to
the failing one; the three together are 16 lines, 2,585 bytes (`elab.sl:651-666`). In the function, the three
rules are one branch of 22 lines, 2,064 bytes (`elabfn.sl:2007-2028`), after an 11-line prefix shared with
the constructor-application rules (`elabfn.sl:1966-1976`). The call rule also rests on helper judgments:

| piece | relation | function |
|---|---|---|
| a call's rule and its two error rules | `elab.sl:651-666`, 2,585 B | `elabfn.sl:2007-2028`, 2,064 B |
| arguments against a telescope | `ElabExprArgs`, `elab.sl:833-863`, 4,447 B | `elab-expr-args`, `elabfn.sl:2035-2081`, 4,593 B |
| the decrease check | `Decrease`, `elab.sl:867-911`, 7,224 B | `decrease`, `elabfn.sl:2083-2137`, 5,284 B |
| a match and its six error rules | `elab.sl:671-702`, 5,197 B | `elab-match`, `elabfn.sl:2139-2169`, 3,383 B |
| branches | `ElabBranches`, `elab.sl:945-996`, 8,628 B | `elab-branches`, `elab-branch`, `elabfn.sl:2170-2220`, 5,848 B |
| evaluation | `eval.sl:6-36`, 3,394 B | `eval.sl:52-125`, 4,864 B |

So rule for rule, the function is about the size of the relation, and for judgments with many error rules it
is smaller, because the function shares the successful prefix across its error exits while each error rule
restates it.

Over the whole of `mini/`. `[RAN] python3 -I closure.py` and `python3 -I split.py`. The split of ADTs into
"what the statements are made of" and "what the functions need" is mechanical: an ADT is on the first side
when it is reachable from `ElabProgram`, `Fails`, or `Eval` by "A's definition mentions B". That this is the
right notion of "the spec" is `[INFERENCE]`; it puts `Closed` and `Scoped` on the function side, which
agrees with `[QUOTE mini/README.md:30-33]` "then, for the functions only, what it means for terms, rules,
names and ADTs to mention only the context's entries and, at a depth, only the binders above it (`Scoped
ents d t`), and for one context to have grown from another."

| | ADTs | constructors | lines | bytes |
|---|---|---|---|---|
| relations reachable from the top-level statements | 179 | 662 | 1,667 | 186,107 |
| function-side ADTs (decision results, invariants, the nested unification walk) | 176 | 374 | 912 | 86,290 |
| run-time (`many`) functions | | | 2,323 | 203,169 |
| erased functions (lemmas) | | | 1,339 | 131,344 |

Ratios: run-time functions to reachable relations, 1.09 by bytes and 1.39 by lines; everything on the
function side to reachable relations, 2.26 by bytes and 2.74 by lines. `[RAN]` arithmetic on the table.
With no classification at all, `split.py` counts 3,662 lines of functions (334,513 bytes) against 2,558
lines of ADT declarations (272,835 bytes): 1.43 by lines and 1.23 by bytes. `[RAN]` The
reachable relations are mostly `elab.sl` (134 KB of the 186 KB). The lemmas are mostly in `ctx.sl` (49 KB),
`elabfn.sl` (39 KB), and `unify.sl` (24 KB).

Error rules. `[RAN] python3 -I errshare.py mini/elab.sl`: in the eighteen judgments whose outcome can be an
error, 58 rules conclude in success (35,099 bytes) and 110 conclude in an error (53,302 bytes). `ElabExpr`
alone is 12 and 27. In `Unify`, 11 and 13.

Other measures of repetition. `[RAN]` `grep -o ... | wc -l` over `mini/*.sl`: 8,949 occurrences of `(erased`;
the seven context fields are spelled out as erased parameters 25 times and destructured by `let-match` 26
times; 328 runs of seven or more `_` arguments; 964 `let-match`, 496 `match`, 64 `absurd` branches,
191 `notail`.

### 2.8 The gap between MINIMAL.md and the full language

What MINIMAL.md removes. `[QUOTE MINIMAL.md:12-47]`

> 1. **Erasure** (sections 13, 14, 21, OPEN.md 2): every multiplicity annotation, `erased`/`many` on telescope
>    entries, `let` binders, matches, `def-fns` lines and `def-adts` constructors; phantom constructors;
>    `union` and the `enum` token, every type now carrying a tag; the one-real-branch counting rules;
>    `coerce`, `Coercible`, the `coercible-*` forms, `newtype` and `Newtype`; `tail` and `delegate`.
> 2. **`Matchable`** (sections 8, 24): `open-adt`, `open-absurd`, `matchable-of`, `newtype-of` and the opening
>    invariant. A `match` instead requires its scrutinee's type to canonicalize to an application of a type
>    constructor declared by a `def-adts`; constructor disjointness (section 7's failure mode 2) reads that
>    declaration. A scrutinee whose type is headed by a variable, a first-class `TyCtor` parameter say,
>    cannot be matched.
> 3. **`else`** branches, **`let-match`** and **`level-of`**, all expressible or unneeded without erasure.
> 4. **`Settled`** (sections 6, 28, 29): the `Settled`/`Hypothetical` state, stored values, run-position
>    statements running during elaboration, the compile-time round trip of DESIGN.md section 29,
>    `comptime-match`, state-forwarding `let`, macros, and `Special` as a value. Special forms are reserved
>    keywords, no longer renameable. Elaboration is a pure function from raw syntax to core terms; evaluation
>    is a separate phase after it.
> 5. **The `_` sugar** of DESIGN.md sections 46 to 53, the `_` level, the `_` annotation and the inferred
>    decrease annotation included: every call in a body writes `(predates p)` or `(subterm p)`, as DESIGN.md
>    section 19 has it.
> 6. **`extern`** and the FFI; there is no prelude, a program declares its own `Nat`.
> 7. **Literals**: numerals, characters, strings.
> 8. **The `absurd` marks** on functions and branches. Ex falso is a match with no branches on a value of a
>    type with no constructors, which the current interpreter already accepts (checked by running one);
>    structural refutation of an unlisted constructor stays, as does the rule that every constructor is
>    listed or refuted.
> 9. **Nested `def-adts`**: a `def-adts` is confined to the top level. `def-fns` and `def-lvl` may still nest
>    inside a body, which the factory pattern of section 57 needs.

MINIMAL.md says of itself: `[QUOTE MINIMAL.md:5-7]` "The cuts are the owner's decisions of one design
session; the wording, and every claim about what a cut takes with it, is that session's reading and may be
mistaken." The list does not mention uniqueness, cells, slots, or `at` (§13, §15, §16, §22, §23, §32, §35 to
§41, §66 to §70); `mini/` has none of them (`[RAN]` the grep in section 2.4). Whether MINIMAL.md means them to
fall under item 1 is `[UNKNOWN]`.

Scale indicators. `[RAN]`

- The DESIGN.md sections that `mini/`'s comments cite (§5, §7, §9 to §12, §17 to §21, §24, §26, §27, §30)
  span 640 of DESIGN.md's 3,157 lines, by the heading line numbers from `grep -n "^## " DESIGN.md`. `mini/`
  covers those sections only in their cut-down form.
- The reference implementation is 6,639 lines, 416,912 bytes of OCaml (`wc lib/*.ml`); `slc` is 18,652
  lines, about 1.41 MB of Sleight (`wc self/*.sl`); the prelude is 2,881 lines. `mini/` is 6,849 lines,
  0.64 MB for its fragment.
- 740 of the 1,337 files in `tests/` carry an `; error:` line, with 758 distinct leading texts
  (`grep -c "; error:" tests/*.sl`; `grep -h "^; error: " tests/*.sl | sed 's/<\*\*>.*//' | cut -c1-60 | sort
  -u | wc -l`). `mini/` has 15 `Reason`s and 110 error rules.

Per feature: does it add rules to the relations `mini/` has, or force them to be restructured? Every entry in
the right-hand column is `[INFERENCE]`. Each rests on the DESIGN.md text quoted or cited beside it and on the
shape of `mini/`'s relations as read; none was tested by writing rules.

| feature | what DESIGN.md says | effect on `mini/`'s relations |
|---|---|---|
| Multiplicities and erasure (§13, §14) | `[QUOTE DESIGN.md:523-525 §14]` "Every binder declares its multiplicity, so the erasure of every name is known where the name is bound, and the erasure of an expression is fixed by the position it occupies." | **Restructures.** `Entry` gains a multiplicity (touching the nine `X`/`XList`/`XTele` relation families and twenty function triples over `Term`), every expression judgment gains a position index, and a new relation from elaborated code to stripped code is needed, because in §27 a run-position form's "erased positions are stripped" before it runs. The rules multiply (phantom branches, one-real-branch). |
| Uniqueness, `share` (§15, §16, §22, §23, §32) | `[QUOTE DESIGN.md:620-621 §15]` "Each binder is checked by the uses it has on each path through the code." | **Restructures.** A usage state must be threaded through every expression rule and joined across match branches (§15: "the maximum of its states after each branch"). `mini/`'s context has no such component. |
| Cells, slots, `at` (§35 to §41, §66 to §70) | `[QUOTE DESIGN.md:1547-1549 §35]` "Every entry of the scope environment (§5), including erased entries, is created together with an anonymous entry of type `(Slot)` at the entry's own erasure." `[QUOTE DESIGN.md:1461-1462 §33]` "Values have a uniform representation: every value is one word, either an immediate or a pointer to a block, whatever its type." | **Restructures the run, extends the checker.** `Eval` over value trees cannot say "at the same slot", cannot do `cell-write` in place, and cannot give `slot-eq` a meaning. A machine with words and blocks replaces `core.sl` and `eval.sl`. On the checking side, slots are atoms of the same fact table, so `Canon` and `Unify` mostly gain rules; `Mint` changes (every entry gets a slot). |
| `Matchable` (§8, §24) | `[QUOTE DESIGN.md:343-344 §8]` "A `Matchable` does nothing just by being in scope. Nothing consults it until it is **opened**." | **Restructures part of `Unify` and the match rule.** `mini/`'s `KDecl` kind, its `adts` list, and `URigidRigid` are replaced by opened first-class objects and the opening invariant, which itself unifies. `Covered`, `Refuted`, and `ElabBranches` keep their shape. |
| `Settled`, run position, `comptime-match` (§5, §6, §27 to §29) | `[QUOTE DESIGN.md:1178-1183 §27]` "**Run position.** A form is in run position when it is under no function body and no match branch. Such a form runs as soon as it has been elaborated, before the code after it is checked: it is elaborated, its erased positions are stripped, the evaluator runs the code, and its results become `Settled` with the resulting values (§29)." `[QUOTE DESIGN.md:1298-1301 §29]` "**The round trip.** Checking a run-position form is a dialogue. The elaborator checks the form and produces code with the erased positions removed. The evaluator runs that code. The resulting values come back to be stored (§5) and embedded as constants." | **Restructures, and changes the theorem.** The elaboration relation gains premises that mention the run relation, entries gain a state and a stored value, and the context gains the program store. For ordinary code the dependency is one way: elaboration mentions the run, and the run of stripped code does not mention elaboration. The macro-world primitives are the exception, since they check as they run: `[QUOTE DESIGN.md:2934-2936 §65]` "`settled-eq` answers `ESome` exactly when the terms the two handles denote, and their types, are identical after canonicalizing against the facts of the innermost run position enclosing the call" and, of `settled-ty-apply`, `[QUOTE DESIGN.md:2981-2982 §65]` "Where it runs, the application is checked again, against the facts `settled-eq` reads." So where macros are involved the run relation mentions canonicalization and term checking, and the two sides depend on each other. In either case the deriving function must call an evaluator, so "the elaborator is total" depends on the run terminating; this is the handoff's item 4. `mini/`'s "elaboration recurses on the raw syntax alone" no longer describes it. |
| Head dispatch, `Special` as a value (§6, §19) | quoted in section 2.2, option 3 | **Restructures.** Which rule applies to a list is decided by a `Settled` head's stored value, not by a keyword in the syntax. `mini/`'s `Key` type and every rule that matches on `RKey` change. |
| Macros (§62 to §65) | `[QUOTE DESIGN.md:2737-2741 §62]` "A list whose head dispatches as a macro is a macro call (§6, §19). The function is applied to a macro world (§65), the position of the call's opening `(` or `$`, and the call's arguments as `Raw` (§63), unexpanded and unresolved; the head is not passed. The forms it returns replace the call." `[QUOTE DESIGN.md:2752-2753 §62]` "At most 10000 expansions run in one run, every file on the command line included." | **Restructures the function, adds rules to the relation.** The forms a macro returns are not subterms of the input, so the elaborator cannot recurse on syntax alone. The specification's own limit of 10,000 expansions gives a measure that needs no extra fuel: remaining expansions, then syntax. The macro world becomes part of the judgment's state: `[QUOTE DESIGN.md:2882 §65]` "The macro world is the elaborator's program store" and `[QUOTE DESIGN.md:2884-2885 §65]` "It is threaded sequentially through all of elaboration". |
| `_` sugar and metas (§46 to §53) | `[QUOTE DESIGN.md:2313-2314 §50]` "Each such `_` is a fresh unification variable, a **meta**." `[QUOTE DESIGN.md:2322-2323 §50]` "The expectation passes down through `values`, `tail`, `notail`, `delegate` and `at`. It never passes up." | **Restructures expression judgments, extends `Unify`.** An expected telescope becomes an input of the expression judgments, and `Unify` gains a kind of variable that "never reaches the fact table". §46 to §48 and §52 read as rewrites and mostly add rules. |
| `extern` and the FFI (§42, §43) | `[QUOTE DESIGN.md:1951-1955 §42]` "An `extern` implementation must agree with its model: except through `slot-eq` (§67), running the models instead of the implementations must give a program the same values, though not the same cost, and either may crash where the other does not (§31)." | **Adds rules, if the spec runs the models**, since a model is ordinary code. The prelude (2,881 lines) then becomes part of the initial context that the formal spec fixes. `World`, `Program`, and `world-do` need a model of the outside. |
| Literals (§45) | `[QUOTE DESIGN.md:2200-2201 §45]` "**What the checker sees.** A numeral is opaque: a `Settled` `Nat` with no `is` rule, next to its erased `Numeral` proof." | **Adds rules, but only after `Settled` exists.** Interning adds a table to the state, and §7's ordering of literals touches `Orient`. `prove-literal-lt` "relies on the evaluator (§29)". |
| `coerce` (§33, §34) | `[QUOTE DESIGN.md:1367-1369 §33]` "A `coerce` reinterprets one value as another value with the same runtime representation, at no runtime cost, on the strength of an erased proof that the two are coercible (§60)." | **Adds rules to checking** (nine proof forms, one expression). Its soundness is a statement about the representation, so it constrains the machine's definition of a word. |
| `absurd` marks, `else`, `let-match`, nested `def-adts` (§21, §25, §27, §51, §52) | | **Adds rules.** `let-match` reuses the refutation test `mini/` already has. |

One consequence for the owner's item 3. In `mini/`, "accepted or rejected" can be total because elaboration
never runs anything. In the full language a run-position form runs during checking, so either the relation
gets a third outcome for a compile-time run that does not finish, or the theorem takes a hypothesis, or
termination of accepted compile-time code is proved first. `[INFERENCE]` from §27 and §29 as quoted. The
handoff records that the owner said "I think I'm in general agreement" to the hypothesis form and that this
"is not agreement to exact statements".

## 3. Part 2: precedents

Sizes are `[RAN] find <dir> -name '*.sl' | xargs cat | wc -lc`. "goal/qed" is `[RAN] grep -rn -E '^\(goal
|^\(qed ' <dirs>`. "native" is `[RAN] grep -rl native-compute`. Times are `[RAN]` on this VM (4 cores; other
agents were running; load average noted per run); the two heavy runs were under `nice -n 10`.

| directory | `.sl` files, lines, bytes | top-level theorem | `goal`/`qed` | `native-compute` | check time here |
|---|---|---|---|---|---|
| `stlc/` | 15; 1,191; 70,980 | `StronglyNormalizing`, `BoundedReductions` | yes, two units, `goal erased` | no | both units: 1.33 s reference, 0.92 s `slc` |
| `higman/` | 18; 2,371; 152,447 | `Higman`, `HigmanK k` | yes, `goal many` | no | two letters: 0.65 s reference, 0.45 s `slc`; k=3: 1.00 / 0.76; k=5: 1.05 / 0.71 |
| `bb/` | 35; 19,885; 1,451,289 (the BB(5) unit: 28 files, 15,399 lines) | `BusyBeaver 5 47176870` | yes, `goal erased` | yes | `slc`: 3 min 25 s wall, 413.6 s user, 282 MB peak |
| `fourcolor/` | 161; 66,776; 5,362,174 (the `FourColor` unit: 142 files, 64,979 lines) | `FourColor` | yes, `goal erased` | yes | `slc`: 1 min 40 s wall, 256.1 s user + 12.0 s system, 1.39 GB peak |
| `heapsort/` | 6; 686; 46,320 | `Heapsort` (in the agent task's spec) | goal in `agent/tasks/heapsort-fast/spec.sl:102`; no `qed` under `heapsort/` | no | reference, check and build: 1.67 s; the program: 0.47 s |
| `msort/` | 4; 361; 19,850 | the type of `msort` | no | no | reference: 0.46 s (command is mine, none is documented) |
| `pal/` | 7; 1,910; 94,344 | the type of `longest-palindrome-manacher` | no | no | reference: 0.89 s; `slc --interpret`: 0.64 s |

### 3.1 `stlc/`

- **Statement, README.** `[QUOTE stlc/README.md:43-49]` "[`spec.sl`](spec.sl) sets the goal
  `StronglyNormalizing`: - some predicate `P` on terms - holds of every typed term (`typed`), - and, whenever
  `P t` holds by a derivation `d` and `t` steps to `u`, holds of `u` by a derivation that is a strict
  `Subterm` of `d` (`step`)."
- **Statement, code.** `[QUOTE stlc/spec.sl:1-8]`

  ```
  (def-adts $ (StronglyNormalizing : -> Type)
    enum
    (many MkSN : (erased (TyCtor ((Term) t) -> Type) P) (erased (Level) L)
       (erased (Fn L (erased (List (Ty)) g) (erased (Term) t) (erased (Ty) a) (erased (Typed g t a) h) -> (erased (P t) d)) typed)
       (erased (Fn L (erased (Term) t u) (erased (P t) d) (erased (Step t u) s) -> (erased (P u) e) (erased (Subterm (P u) e (P t) d) dec)) step)
       -> (StronglyNormalizing)))

  (goal erased (StronglyNormalizing))
  ```
  discharged by `[QUOTE stlc/qed.sl:1]` "(qed (MkSN Sn (level-of typed-normalizes) typed-normalizes
  sn-reduct))". The second unit's goal is `BoundedReductions` (`[READ stlc/ispec.sl:92-98]`), discharged at
  `stlc/iqed.sl:9`.
- **How it is stated.** `--goal proved`, DESIGN.md §71. `[QUOTE stlc/check.sh:6]` "$RUN $PROOF stlc/spec.sl
  $LEMMAS stlc/qed.sl --goal proved \"$@\" &&". A universally quantified statement is a function packed with
  its level in a one-constructor ADT, as §71 prescribes: `[QUOTE DESIGN.md:3134 §71]` "A goal is one type,
  not a telescope; an existential, such as a function with its level, is packaged by an ADT (§21)."
- **`native-compute`.** None. `[RAN] grep -rl native-compute stlc` is empty.
- **Check.** `[RAN] SLEIGHT=/home/user/sleight/_build/default/bin/main.exe sh stlc/check.sh` printed
  `--goal proved: PASS` twice, `real 1.33`; with `SLEIGHT=/home/user/sleight/_build/release/slc`, the same,
  `real 0.92`. (The script's default is `dune exec`; I overrode it and ran no dune.) With either compiler the first unit prints 13
  lopsided-match warnings, and the second prints 17 of those and four shadowing warnings.
- **Object terms.** Two representations. Curry-style: `Term` is `Var Nat`, `Lam Term`, `App Term Term`, with
  de Bruijn indices. `[READ stlc/curry.sl:1-5]` Intrinsic: `(Term g a)` indexed by context and type, a
  variable being a membership proof `(Mem g a)`. `[READ stlc/ispec.sl:1-10]`
- **Typing.** `Typed : ((List (Ty)) g) ((Term) t) ((Ty) a) -> Type` with rules `TyVar` (through the
  prelude's `Nth`), `TyLam`, `TyApp`. `[READ stlc/curry.sl:36-42]` The intrinsic terms need no judgment.
- **Reduction is small-step.** `Step : ((Term) t) ((Term) u) -> Type` with `StBeta`, `StLam`, `StAppL`,
  `StAppR`: one step of full β-reduction, under binders and on both sides of an application.
  `[READ stlc/curry.sl:29-34]` Shifting and substitution are relations too (`Shift` through `Skip`, `Sub`),
  with existence and determinism lemmas beside them (`shift-ex`, `shift-det`, `sub-ex`, `sub-det`).
  `[READ stlc/curry.sl:7-27; stlc/subst.sl:1, 10, 27, 41]` The intrinsic statement has `OneStep` and a
  step-counted `Reduction g a k t u`. `[READ stlc/ispec.sl:64-84]`
- **Structure of the argument.** `[READ stlc/jm.sl:1-75; stlc/reducts.sl; stlc/proof.sl]` and
  `[QUOTE stlc/README.md:74-79]` "typed terms are in `SN`, an inductive characterization of strongly
  normalizing terms indexed by context and type, with neutral terms (`SNe`) and strong head reduction
  (`SNRed`). The main block proves closure under substitution (`sub-sn`, `sub-ne`, `sub-red`) and under
  application (`app-sn`), by lexicographic recursion on the type of the substituted variable and then on the
  derivation." Then `Sn t` holds the list of all one-step reducts of `t`, each `Sn`
  (`[READ stlc/reducts.sl:175-182]`); `sn-step` returns the reduct's derivation with a `Subterm` proof
  (`reducts.sl:193-197`); `sn-of` takes `SN` to `Sn` (`proof.sl:56-77`). The whole proof is `erased`
  functions: `[RAN]` 84 erased function headers and 0 `many` ones under `stlc/`.
- **A constraint the README states**, relevant to any accessibility-style statement about Sleight's own
  evaluation: `[QUOTE stlc/README.md:59-62]` "A function-valued accessibility predicate, `(Acc t)` holding a
  function from each step `t → u` to `(Acc u)`, would not do here. A closure at a fresh level can call the
  function that builds it, so such a value can be built for a relation that loops."
- **What transfers.** `[INFERENCE]`, from reading both developments.
  - The method transfers whole: judgments as ADTs, `-ex` and `-det` lemma pairs, induction on a derivation
    with `subterm erased`, a goal packed with `level-of`.
  - The de Bruijn code does not. `stlc/` substitutes one variable with shifting (`Skip`, `Shift`, `Sub`, and
    five commutation lemmas). `mini/` chose otherwise: `[QUOTE mini/README.md:116-119]` "**Substitution
    without arithmetic.** A substitution is a list indexed by `Bound`, a `None` standing for a binder passed
    on the way in, so going under a telescope entry is prepending a `None` and nothing is ever shifted;
    abstraction is the same list over entry ids." Free variables in `mini/` are global entry ids, not indices.
  - The normalization technique does not obviously apply. It is induction on simple types; Sleight has
    `[QUOTE DESIGN.md:438-439 §10]` "There is no universe stratification, and no positivity requirement on
    function or datatype signatures." and rests termination on levels (§17). `stlc/README.md:102-106` itself
    calls its choice of technique "a reading of why it fits".
  - The size is a calibration point: 54 lines of statement (`types.sl`, `curry.sl`, `spec.sl`) against 823
    lines of proof for the first unit (`skip`, `ctx`, `subst`, `jm`, `reducts`, `steps`, `proof`, `qed`).
    `[RAN] wc -l stlc/*.sl`

### 3.2 `higman/`

- `[QUOTE higman/README.md:10-15]` "`spec.sl` sets the goal `(goal many (Higman))`. A `Higman` holds a
  factory. Given only the level `M` of a sequence, it returns a level `L` and a search at `L`. Given a
  relation `G` and a sequence `f : (Fn M (many (Nat) i) -> (many (List (Bool)) w) (erased (G i w) g))`, the
  search returns indices `i < j`, two words `u` and `w` with `G i u` and `G j w`, and a proof `(Emb u w)`
  that `u` is a subsequence of `w`."
- In code: `Higman` at `higman/spec.sl:14-23`, the goal at `spec.sl:25`, the `qed` at `higman/higman.sl:35`;
  `HigmanK` at `higman/kspec.sl:19-28`, its `qed` at `higman/ksearch.sl:36`. `[READ]`, `[RAN] grep`
- `[QUOTE higman/README.md:24-25]` "The proof uses no axioms and no `native-compute`. It appears to rest only
  on the compilers' type checking."
- A statement about a function that cannot name the function's result in a type, because
  `[QUOTE higman/README.md:17-18]` "A type holds no call (DESIGN.md §9), so the statement cannot name `(f i)`.
  `G` ties each word to its index instead". The same device would be needed to state anything about what a
  compiler function returns. `[INFERENCE]`
- `[RAN] sh higman/check.sh slc`, `ref`, `slc 3`, `ref 3`, `slc 5`, `ref 5`: each printed `--goal proved:
  PASS`; times in the table.

### 3.3 `bb/`

- `[QUOTE README.md:84-85]` "[`bb/`](bb/) proves that the fifth busy beaver value is 47,176,870".
  `[QUOTE bb/README.md:10-11]` "`agent/tasks/bb5/spec.sl`, the goal `BusyBeaver 5 47176870` over the
  definitions in `agent/tasks/bb5/defs.sl`. This is the recommended one."
- In code: `[QUOTE agent/tasks/bb5/spec.sl:1]` "(goal erased (BusyBeaver 5 47176870))"; `BusyBeaver` at
  `agent/tasks/bb5/defs.sl:65-72`: a champion machine, a proof that it halts from the blank tape in exactly
  `v` steps, and a function at some level giving `NatLe k v` for every machine and every `k` with a halting
  proof. The `qed` is at `bb/spec5.sl:26`. `[READ]`
- The machine semantics there is a small-step relation with a step-counted halting relation: `Step` and
  `HaltsIn n m c k`. `[READ agent/tasks/bb5/defs.sl:42-61]`
- `native-compute`: yes. `[RAN] grep -n native-compute bb/*.sl` finds eight uses, among them
  `bb/spec5.sl:17`. The pattern is a `many` checker that returns evidence, run natively, then read back by
  `comptime-match`: `[QUOTE bb/spec5.sl:17-18]` "(let ((many spec-res)) (native-compute run-champ))
  (comptime-match many spec-res (ROk _ champ-h))". `[QUOTE DESIGN.md:3152-3153 §72]` "The compiled run hands
  back only the constructor, so its erased fields take the tokens of §5."
- `[RAN]` the README's recommended command with `_build/release/slc` (28 files, `--goal proved --inline
  25`), under `nice -n 10`, load average 1.25 at the start and about 6 during: `--goal proved: PASS`,
  elapsed 3:25.32, user 413.60 s, system 3.96 s, 203% CPU, maximum resident set 282,212 KB.
  The README's own figure: `[QUOTE bb/README.md:38]` "The check took about 36 s there." (a 12-core Mac).

### 3.4 `fourcolor/`

- `[QUOTE fourcolor/README.md:11-16]` "`fcfinal.sl`: the goal `(goal erased (FourColor))`, with `FourColor`
  as `defs.sl` states it: every drawing (a list of straight edges between distinct points, any two of them
  compatible in the sense of `defs.sl`'s `Compatible`, which appears to mean they meet at most at a shared
  endpoint) has a colouring of its points with four colours in which the endpoints of every edge differ."
- In code: `[QUOTE fourcolor/defs.sl:98-103]`

  ```
  (def-adts $ (FourColor : -> Type)
    enum
    (many MkFourColor : (erased (Level) L)
        (erased (Fn L (erased (List (Edge)) es) (erased (Drawing es) drawn) ->
            (erased (List (Paint)) ks) (erased (Proper ks es) proper)) thm)
        -> (FourColor)))
  ```
  Goal and `qed` at `fourcolor/fcfinal.sl:1-2`.
- `native-compute`: yes. `[QUOTE fourcolor/README.md:70-72]` "All the checks run inside one `native-compute`
  (`native.sl`). It writes one OCaml program of about 2 MB, compiles it once, and runs its 154 jobs as
  separate processes, as many at a time as there are cores."
- `[RAN] sh fourcolor/check.sh final slc` under `nice -n 10`, load average 5.75 at the start: `--goal
  proved: PASS`, elapsed 1:39.80, user 256.09 s, system 12.02 s, 268% CPU, maximum resident set
  1,390,516 KB. The README's own figures for a 4-core cloud VM: `[QUOTE fourcolor/README.md:82]`
  "| `FourColor` | slc | about 3 min | about 9.5 min | about 1.2 GB |", and of the split,
  `[QUOTE fourcolor/README.md:85-86]` "On the VM with slc, about 30 s of the time is elaboration and about
  10 s is ocamlopt; the rest is the jobs". I did not measure the split.

### 3.5 `heapsort/`, `msort/`, `pal/`

- **`heapsort/`.** `[QUOTE README.md:76-78]` "[`heapsort/`](heapsort/), an in-place heap sort certified
  against [`agent/tasks/heapsort-fast/spec.sl`](agent/tasks/heapsort-fast/spec.sl) and timed against OCaml
  and Lean". The statement is `Heapsort` with `(goal many (Heapsort))`. `[READ agent/tasks/heapsort-fast/
  spec.sl:92-102]` The sort's own type is at `heapsort/flat/sort.sl:1-5`. No file under `heapsort/` has a
  `qed` (`[RAN]` the grep above), and the documented command builds and runs a benchmark; it does not pass
  `--goal proved`. `[READ heapsort/flat/README.md]` `[RAN]` that command with the prebuilt reference in place
  of `dune exec bin/main.exe --` and the output in my scratch directory: exit 0 in 1.67 s; the program
  printed `checksum 393660565753209066784` and `minor-words 0`, in 0.47 s.
- **`msort/`.** `[QUOTE README.md:78-79]` "[`msort/`](msort/), an in-place merge sort on unique lists
  certified against [`msort/spec.sl`](msort/spec.sl)." The theorem is the function's type:
  `[QUOTE msort/msort.sl:123-124]` "(def-fns _ $ (many msort : (unique (ULst) xs) (erased (Nat) len) (erased
  (LenU xs len) l) (erased (Lt len u62-modulus) b) -> (unique (ULst) r) (erased (SortedU r) s) (erased (PermU
  xs r) p))". No `goal`, no README, no documented command. `[RAN] main.exe msort/spec.sl msort/lemmas.sl
  msort/msort.sl`: exit 0, 0.46 s. (`--no-extern` on the same files segfaulted the reference after 1.19 s;
  that flag was my addition and I did not investigate.) `msort/main.sl:45` ends in `(Continue Main start)`,
  a small example of a program whose final value is a `Program` for the driver.
- **`pal/`.** `[QUOTE pal/README.md:3-4]` "`longest-palindrome-manacher` in `palindrome_manacher.sl`
  implements Manacher's algorithm and has this interface:" and `[QUOTE pal/README.md:7-8]` "(many (List (Nat))
  xs) -> (many (Nat) n) (erased (LongestPalindrome xs n) correct)". The function is at `pal/palindrome_manacher.sl:249` and
  the relation at `pal/palindrome_relations.sl:194`. No `goal`. `[RAN]` the README's command with the
  prebuilt reference: exit 0, 0.89 s, last line equal to `tests/palindrome_manacher.sl`'s `; expect:` (compared by the
  shell, and likewise for `slc --interpret`).

### 3.6 What the precedents say about stating a compiler theorem

`[INFERENCE]`, from the statements above. Three forms are in use, and `mini/` already uses the first:

1. **The function's type is the theorem** (`pal/`, `msort/`, `mini/`'s deriving functions). A `many`
   function returns its result with an erased derivation. For a compiler: `compile` returns an outcome and a
   derivation that the source has that outcome under the spec.
2. **A goal that packs a function with its level** (`stlc/`, `higman/`, `fourcolor/`, `bb/`). This is how
   the same statement would be put under `--goal proved`. `higman/` shows a `goal many` whose function is a
   program that runs.
3. **A checker run by `native-compute` and read back by `comptime-match`** (`bb/`, `fourcolor/`). This is
   for large finite checks. It adds the compiled run to what the proof rests on:
   `[QUOTE DESIGN.md:1307-1309 §29]` "A stored value that `native-compute` produced relies on its compiled
   run in the same way (§72)."

### 3.7 Cost data from agent runs

`[RAN]` a Python summary of `heapsort/agent-runs-8860c75.csv` (28 runs of the heapsort-fast task, whose goal
is the `Heapsort` statement above). 25 runs have a passing session and 3 (`gpt-6-luna`) have none. Among the
passing runs: solutions of 836 to 3,155 lines; run cost at the first pass from 2.18 to 15.76 dollars. The
three `claude-opus-5-5` runs passed in their first session, at 4.67, 5.73, and 6.15 dollars, with 836, 922,
and 940 lines and 24% to 28% of the context window; the three `claude-sonnet-5-5` runs likewise in the first
session, at 4.77 to 5.34 dollars. What the file is: `[QUOTE heapsort/README.md:30-33]` "A Claude session
derived it by re-checking each session with slc built at that commit and reading the erased OCaml of each
first pass to judge that it is a heap sort; that judgment and the `notes` column are its reading and may be
wrong."

The effort that went into `mini/`, `stlc/`, `bb/`, and `fourcolor/` is `[UNKNOWN]`. The clone has 50 commits
(`[RAN] git log --oneline | wc -l`), and `mini/` appears in one of them.

## 4. Part 3: idioms, with examples

Each is `[READ]` at the lines given. The explanations cite DESIGN.md only where I checked the text.

1. **A relation is an ADT whose constructors are the rules; everything a rule mentions is an erased field.**
   `mini/canon.sl:38-55` (`Canon`). An index that the conclusion fixes is written in the constructor's
   return type.
2. **A deriving function returns the data with an erased derivation, through multiple returns.**
   `mini/term.sl:96`: `subst` returns `(many (Term) u) (erased (Subst subs t u) p)`. The caller takes them
   apart with a `let`: `mini/term.sl:107`, `(let ((many h2) (erased p)) (notail $ subst subs n ln h ch))`.
3. **A decider returns a two-constructor ADT with evidence on both sides.** `mini/base.sl:9-18` (`NatDec`,
   `nat-dec`); `mini/ctx.sl:41-52` (`EntDec`, `ent-dec`); `mini/elabfn.sl:372-389` (`MemDec`, `mem-dec`). The
   negative side needs its own relation (`Neq`, `NoEnt`, `NotMem`).
4. **A judgment that can fail carries its outcome as an index, so success and failure are one relation.**
   `mini/elab.sl:199-202` (`TOut`), `mini/elab.sl:1239-1241` (`Fails`).
5. **`let-match` with a branch that returns early.** `mini/base.sl:78-79`: `(let-match many xs (Cons _ x
   rest) ((Nil _) (values (Zero) (LengthNil _))))`. The pattern's fields stay in scope for the rest of the
   body; the other branch ends the function. DESIGN.md §52.
6. **Inverting an erased derivation with a bare `let-match erased`.** `mini/term.sl:106`: `(let-match erased
   ct (ClTyApp _ _ _ _ out ch cps cas))`. The other constructors are refuted by their indices, so no branch
   is written. `[QUOTE DESIGN.md:1138-1140 §27]` "It
   requires that exactly one constructor of the scrutinee survives the automatic refutation an ordinary
   `match` applies (§7)."
7. **Refuting an impossible case with a proof of an empty type.** `mini/term.sl:100-101`: `(absurd (NthMiss _
   _ _ p) (let-match erased ct (ClBound _ _ lt)) (no-nth-lt _ subs n k ln lt p))`. The helper is an `absurd`
   function returning `(erased (False) f)`: `mini/base.sl:20-23`, `mini/base.sl:120-126`. DESIGN.md §51.
8. **Induction on a derivation: mark it `subterm erased`.** `mini/canon.sl:272-282` (`canon-canonical`);
   `mini/preserve.sl:18`; `stlc/skip.sl:12-18`. A recursive call on a premise needs no annotation under the
   `_` sugar the files use throughout (§48).
9. **Using an equality: match it against `Refl`.** `mini/preserve.sl:31`: `(let-match erased (canon-unique
   rules h h2 h3 ph qh) (Refl _ _))` identifies `h2` and `h3` for the rest of the body. Where two things are
   equal together, a small ADT stands in for a pair of equalities: `mini/canon.sl:116-118` (`SameRank`),
   `mini/ctx.sl:516-518` (`SameEnt`). To carry evidence across an index equality, match the evidence under an
   explicit return annotation: `mini/ctx.sl:840`.
10. **Mutual recursion is one `def-fns` with several functions, and mutually recursive relations are one
    `def-adts`.** `mini/term.sl:95-148` (`subst`, `subst-list`, `subst-tele`); `mini/canon.sl:37-65`.
    Same-level calls are marked `notail` or `tail` (WARNINGS.md 4): `mini/term.sl:107`, `mini/core.sl:96`.
11. **A termination measure that is not a syntactic subterm: an erased `Nat` with evidence, and `(subterm
    proof)` at the call.** `mini/canon.sl:201` (`(subterm (lt-subterm k n lt))`); `mini/unify.sl:850`. For a
    piece of the argument reached through a helper, `prove-subterm` and `subterm-trans`:
    `mini/elabfn.sl:713`, `mini/elabfn.sl:988`, `stlc/reducts.sl:187-191`.
12. **Invariants travel beside the data.** `mini/elabfn.sl:8-13` (`WF ctx`), taken and returned by every
    elaboration function, with `Grew` evidence for the new context: `mini/elabfn.sl:34-35`.
13. **A function to be held in data is built by a factory and packed with `level-of`.** `stlc/iqed.sl:1-7`
    defines `bound` inside a body and returns `(MkBounded g a t n (level-of bound) bound)`;
    `stlc/qed.sl:1`. DESIGN.md §57.
14. **Several names of one type in one entry.** `stlc/curry.sl:11`: `(erased (Nat) k i j)`. `mini/` spells
    each entry separately, which is part of why its lines are long.

**Pain points the code visibly works around.**

1. **A type holds no call (§9), so every projection is a relation.** `Ents`, `Rules`, `Scope`, `Adts`,
   `LevelOf`, and `SubArgs` are six one-rule relations that read one field of the context, each restating the
   seven fields. `[READ mini/elab.sl:63-86]`
2. **Every rule restates its variables, and every error rule restates the successful prefix.** `EXCall`
   declares 21 variables for 11 premises; `EBRestErr` restates the thirteen premises that precede `EBCons`'s recursive one.
   `[READ mini/elab.sl:651-657, 948-956, 988-996]` Finding 8 has the totals.
3. **"Not this shape" needs a relation per shape with a constructor per alternative, and a decider with a
   branch per constructor.** Six such families (section 2.2), and for example seven near-identical lines at
   `mini/elabfn.sl:1294-1300`. An `else` branch gives no evidence about what was excluded.
4. **Disequality of constructors is coded through numbers.** `ShapeOf` maps each `Term` constructor to a
   unary numeral so that one rule, `UMismatch`, can say two shapes differ. `[READ mini/unify.sl:85-96,
   206-209]` Numerals are written as `Succ` chains, up to seven deep (`mini/unify.sl:885`), since a literal
   is opaque to the checker (§45).
5. **Phase parameters.** `[QUOTE mini/unify.sl:643-644]` "A third subterm argument, a phase, lets a function
   hand its own arguments to a helper (the second can only decrease when the first stays)." The `Phase` type
   exists only for this (`mini/unify.sl:652-655`), and the elaborator's functions take `(subterm erased
   (POuter (PInner)) is _ph)` (`mini/elabfn.sl:830`).
6. **The function cannot follow the relation's recursion, so a second relation and a conversion lemma are
   needed.** `Unify` is a worklist over equations; the function derives the nested `UnifyC` and an erased
   `conv` rebuilds `Unify`. `[READ mini/unify.sl:243-246, 347-450]` This is about 200 lines.
7. **Each relation and lemma over `Term` comes in three forms**: term, list, telescope. Nine relation
   families and twenty function triples, each with a case per `Term` constructor. `[RAN]` the function
   listing by `grep`. Adding a constructor to `Term` touches all of them.
8. **`--warn-unused` forces underscore names for parameters that only order the recursion or pin a type**:
   `_ph`, `_tl`, `_tb`, `_fc`, `_hr`. `[READ mini/elabfn.sl:830, 847; mini/unify.sl:624, 950]`
9. **One flat namespace.** `mini/` prefixes every rule name (`ET`, `EX`, `EB`, `ST`, `BL`, `MF`).
   `stlc/` needs `curry-names.sl` to keep one representation's names reachable after the other reuses them,
   and its second unit prints four shadowing warnings. `[QUOTE fourcolor/WORKAROUNDS.md:52]` "**Names
   collide across the ~140 files of one unit.** All files share one namespace"
10. **A function stored in data cannot be called by earlier code.** `[QUOTE fourcolor/WORKAROUNDS.md:12-15]` "**Functions stored in data cannot be called.** A function that is a field of a value has a level
    that was minted elsewhere, so code defined earlier cannot call it (DESIGN.md §17–§18). Facts are
    therefore given as first-order certificates, not as functions." This is why refutations in `mini/` are
    positive relations (`NoRule`, `Unassignable`, `Differ`) and not functions into `False`. `[INFERENCE]`
11. **One goal per unit.** `[QUOTE fourcolor/WORKAROUNDS.md:46-50]` "**One goal per unit.** A unit may set
    only one goal, so each computed check is split into a proof file, which leaves its proof as a top-level
    value (`red/proof-c.sl`, `red/bproof.sl`, `unav/qztproof.sl`, `embed4proof.sl`, `fcproof.sl`), and a goal
    file of two or three lines."
12. **Comments in `mini/` are not reliable.** `mini/term.sl:7-10` reads "A term has-is closed except"
    (apparently a mechanical rename of a field `is` to `has-is` that also rewrote the prose; `[INFERENCE]`); `mini/unify.sl:608-610` and `643`
    are one comment split around unrelated code; `mini/elabfn.sl:4-5` names an exception that no longer
    exists (section 2.2). `WithScope` (`mini/elab.sl:106-109`) is declared and never used (`[RAN] grep -n
    WithScope mini/*.sl`).

## 5. Things I am least sure of

1. **That the stuck table is complete.** I read every function that returns a `*Stuck` constructor, and the
   `grep` shows no `Stuck` in the ranges of `elabfn.sl` I did not read except `AtomNamesStuck`, which I did
   read. But I classified "origin" against "passed up" by eye over 174 occurrences, and my eleven runs cover
   9 of the 28 groups.
2. **That no derivation exists for a stuck input.** I did not try to prove it for any group, and one
   counterexample to the general claim existed before (`tests/mini_untyped_rule.sl`). Likewise I did not
   look for a program with two outcomes.
3. **The "restructures or adds rules" column in section 2.8.** It is judgment from reading DESIGN.md once
   and `mini/` once. The entries I trust least are `coerce`, `Matchable`, and the `_` sugar, where I did not
   look at how `lib/` or `self/` implement them.
4. **The reachability split in section 2.7** as a definition of "the spec". It is mechanical, but a relation
   such as `Scoped` that the functions need for totality may turn out to belong in the statements once
   determinism is stated.
5. **The mapping from relations to DESIGN.md sections.** It reports `mini/`'s comments. I verified three
   points against DESIGN.md and found one count that disagrees (three contradictions against four cases) and
   one rule that differs by design (rigid declared atoms).
6. **The heavy timings.** One run each, under `nice`, on a machine other agents were using. The reference
   compiler was not run on `bb/` or `fourcolor/`.
7. **`msort/`'s command** is mine; and the `--no-extern` segfault there is unexplained.
8. **The cost CSV** is a previous session's compilation; I summarized it and verified nothing in it.
9. While I worked, untracked files appeared under `proposals/formalization/` in `/home/user/sleight`
   (`[RAN] git status --short` showed nothing at about 09:49 by the VM's clock and `?? proposals/` at about
   09:57; `ls -la` dates the directory 09:54). I did not create them and did not open them.

## 6. Where DESIGN.md is silent, as far as this task met it

- DESIGN.md does not mention `mini/`, MINIMAL.md, a `Fails` relation, a "stuck" outcome, or the phrase
  "accepted or rejected". `[RAN] grep -n -i "minimal\|mini/\|Fails\b\|stuck\|accepted or rejected\|well-formed"
  DESIGN.md` finds only line 310 ("Forcing fails, ...") and four uses of "fails" in other senses (lines 1857,
  1880, 2965, 2982).
- DESIGN.md has no general statement that every source text is either accepted or refused; each section
  says of its own forms what "is an error". `[INFERENCE]` from having read the whole file once; the grep
  above is the only mechanical check.

## 7. Scratch files and commands

All under `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A3/`.

| file | what it does |
|---|---|
| `run_mini_ref.sh [flags]` | each `tests/mini_*.sl` with its `; needs:` files under the reference; compares the last line with `; expect:` |
| `run_mini_slc.sh interpret\|build` | the same under `slc --warn-unused --interpret`, or `--byte --build` then the program |
| `cumulative.sh` | cumulative load times of `mini/*.sl` under both |
| `adts.py`, `adt-inventory.txt` | every ADT with its index count, constructor count, and line |
| `split.py` | lines and bytes of `def-adts`, `many` functions, `erased` functions, comments |
| `closure.py` | the ADTs reachable from `ElabProgram`, `Fails`, `Eval`, and the rest |
| `errshare.py` | success rules against error rules per judgment |
| `stuck_demo.sl` | the eleven stuck inputs and three controls |
| `fuel_demo.sl` | `eval` under fuel 5, 8, 9, 10, and 500 |
| `heavy.sh` | the BB(5) and four colour checks with `/usr/bin/time -v`, `TMPDIR` in scratch |
| `run/` | every output and error stream, and the built programs |

The binaries used were `/home/user/sleight/_build/default/bin/main.exe` and
`/home/user/sleight/_build/release/slc` throughout. I ran no `dune`, `bootstrap.sh`, or `release.sh`, and no
git command that changes state. `native-compute` in the two heavy checks ran `ocamlfind ocamlopt` in a
temporary directory under my scratch `tmp/`.
