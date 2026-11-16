# A4 — Lessons from the Lean effort (`lean/`) for a formalization of Sleight in Sleight

Read-only analysis. Nothing under `/home/user/sleight` was modified. The lead asked for lessons, not a
blueprint: nothing below recommends copying the Lean design.

Tags: `[QUOTE file:line]` exact text; `[RAN]` a command I ran, with output; `[READ file:lines]` what I
established by reading that code or text myself; `[INFERENCE]` reasoned, not verified; `[UNKNOWN]`.
Paths are relative to `/home/user/sleight` unless absolute. "§N" is a DESIGN.md section.

**What I could not check.** Lean is not installed, so no proof was re-checked:
`[RAN] which lean lake; echo "exit: $?"` printed `exit: 1`; `ls ~/.elan` and `ls lean/.lake` both
answered "No such file or directory". Every claim below that something "is proved" is either a quote from
a session-written README or a `[READ]` of a theorem *statement* in a `.lean` file. Whether `lake build`
passes today is `[UNKNOWN]`. What I can say: `[RAN] grep -rn --include='*.lean' -e sorry -e admit .`
(in `lean/`) printed nothing; `'^axiom '` has 0 hits; `'^opaque '` has 1 (`fixFuel`); `'partial def'` has 66
(Reader.lean 45, Infer.lean 12, Run.lean 9). The toolchain file says `leanprover/lean4:v4.34.1`
`[RAN] cat lean/lean-toolchain`.

**What I read.** In full: `lean/README.md`, `lean/HANDOFF.md`, `lean/TAIL.md`, `lean/WARNINGS.md`,
`SOUNDNESS.md`, `OPEN.md`, `MINIMAL.md`, all of `DESIGN.md` (lines 1 to 3156), and the Lean files
`Syntax`, `Eval`, `Strip`, `Machine`, `Typing`, `Unify`, `Uses`. In part (the statements and definitions
cited below, located by grep): `Check`, `Sound`, `Native`, `Run`, `Reader`, `MachineSound`, `MachineRun`,
`MachineAsm`; `Deleg`, `MachineDeleg`, `UnifySound`, `Lemmas`, and `Infer` only by their lists of top-level
declarations.

---

## 0. The findings that matter most for the decisions

1. **The Lean model is pure-first, with three runs and a fourth executable one.** `eval` (full run: erased
   code runs; a function) `[READ lean/Minimal/Eval.lean:64-115]`; `RunS` (stripped run; an inductive
   relation) `[READ lean/Minimal/Strip.lean:84-103]`; `RunM` (heap machine; an inductive relation)
   `[READ lean/Minimal/Machine.lean:97-126]`; and `runS`/`runA`/`runAM`, the fuelled functions the runner
   actually executes `[READ lean/Minimal/Native.lean:1781-1820, 1934-1987]`. There is no executable machine:
   `[QUOTE lean/README.md:186-187]` "`coerce` and calls through delegates are covered; the runner does not
   yet use the machine run."

2. **Slots are not locations anywhere in the Lean model, so no theorem ties a slot fact to a word.**
   `[QUOTE lean/README.md:537-542]` "`Slot` is a built-in type with one constructor and no `Matchable`, and
   `vacant-slot` is that constructor; a value prints as `_`. In the core a slot is an entry of type
   `(Slot)`, made by `Prim.atom`, which evaluates to the constructor; the core knows nothing of locations,
   and two slots are one exactly when they canonicalize to one entry." Every slot has the same value in all
   three runs `[READ Eval.lean:47; Strip.lean:68-73; Machine.lean:67-69]`, and the core's `Prim.atomEq`
   types an `Eq` proof between *any* two entries of such a one-value type `[READ Typing.lean:421-424;
   Sound.lean:1741-1753]`. So slot facts are vacuously true in the Lean semantics: OPEN.md 3 is made
   trivial there, not answered `[INFERENCE from those READs]`. The session's own list says so:
   `[QUOTE lean/HANDOFF.md:85-88]` "Slots mean words: every slot fact the checker holds (`at` promises,
   forcings, `slot-self`, the writers of DESIGN.md section 36) is true of the words, or reading an `at`
   entry back from its target gives the wrong value." under the heading `[QUOTE lean/HANDOFF.md:83]` "Not
   done, on this session's reading:".

3. **The session found that the location reading cannot be bolted on.**
   `[QUOTE lean/HANDOFF.md:403-406]` "A session's reading is that supporting it would mean the proofs
   tracking slots as locations (live cells whose slot entries canonicalize to one entry being equal
   values), not a case beside the existing ones." (about `cell-same`, §68). This is the most direct
   evidence in the documents for the owner's remark as the handoff reports it:
   `[QUOTE scratchpad/handoff.md:23]` "That work reached a point where the Lean code might be worth
   rewriting, in particular in how it deals with slots and mutation."

4. **In-place mutation in the machine is one operation, driven by marks from the untrusted reader.** The
   only heap overwrite is `Prog.reuse`, at a cell invocation under a pending `Mark.reuse true`
   `[READ Machine.lean:73-95]`. A `cell-write` at `unique` stores nothing: it passes the block's pointer
   through `[READ Machine.lean:92-94]`, although §37 says of it `[QUOTE DESIGN.md:1754, §37]` "This is a
   physical store into memory". `at` is not read back, at-functions and at-matches run, and arrays run
   their models `[READ lean/README.md:575-576, 611-613, 449-452; quoted in sections 1 and 3.4]`.

5. **The machine-agreement proof cost about twice the whole soundness proof.** Machine proofs: 8,827 lines
   (39.0%), 531,403 bytes (42.4%). Full-plus-stripped soundness: 4,630 lines (20.5%), 263,233 bytes (21.0%)
   `[RAN, section 5]`. And what that machine adds to the stripped run is only heap blocks, in-place cell
   invocation, `cell-alloc`, and building only the non-erased arguments of a call
   (`[QUOTE lean/HANDOFF.md:74-76]` "a heap, cell invocations at unique written in place (`Prog.reuse`),
   `cell-alloc` allocating, and a call building only its non-erased arguments").

6. **`eval` has no fuel only because of Lean's logic; everything executable has fuel.** `eval` is
   well-founded recursion on `((⟨μ⟩ : Mu P.k), sizeOf c)` with a *dynamic* decrease check
   `[READ Eval.lean:64-115]`; the lexicographic length `P.k + 1` depends on the object program. `runS`,
   `runAM`, the checker's own compile-time evaluation (`fixFuel`, inside the typing relation), the reader,
   the runner, and the driver all take fuel `[READ/RAN, section 2.6]`.

7. **The theorems start at `Core`, an A-normal core language.** The reader, elaborator, inference, and
   driver (`Reader`, `Infer`, `Run`: 3,907 lines, 66 `partial def`s, `[RAN, section 5 and the preamble]`)
   are outside them: `[QUOTE lean/README.md:215-216]` "The reader and the elaborator, from surface syntax
   to `Core`. The theorems are about `Core` programs." The order among sibling sub-expressions is fixed
   only there (left to right, head first) `[READ, section 4]`.

8. **What the owner's stated goal does not need is most of what the Lean proof is.** The full run, `VTy`,
   `Real`, `eval_sound`, and `no_false` serve soundness and consistency; the handoff says
   `[QUOTE scratchpad/handoff.md:19]` "No `no_false` theorem is expected". And on a machine-first spec the
   slot lemma of finding 2 and the ownership invariant stop being obligations of the agreement theorem and
   become optional theorems about the spec `[INFERENCE, section 7(b) item 2]`.

9. **A Sleight function can run a machine with no fuel by recursing on an erased halting derivation**,
   which I checked on a toy machine with a short program under both implementations `[RAN, section 2.7]`.
   Lean's own mechanism does not carry over `[INFERENCE, section 2.7]`.

---

## 1. What the Lean model covers and what it leaves out

**Its own description.** `[QUOTE lean/README.md:3-10]` "A Lean 4 prototype of a large fragment of the
language of DESIGN.md, the minimal language of MINIMAL.md and the additions listed below: a reader and
elaborator from the full language's surface syntax to a core language, a checker, an evaluator, and
machine-checked theorems connecting the two. Everything here is the work of Claude sessions at the owner's
request; the shapes they chose are listed at the end for the owner to confirm or change. A claim in this
file that the Lean files do not check is a claim of those sessions, and may be mistaken."

**Covered.** The base is MINIMAL.md's fragment; the additions are the README's list under
`[QUOTE lean/README.md:275]` "## Beyond MINIMAL.md". Each item below is a bullet's topic and its starting
line in that list `[READ lean/README.md:275-645]`: multiplicities `erased`,
`many`, `unique` (277); `absurd` (299); `let-match` (309); `_` as an inferred argument (317); literals
(327); a result typed with the program's own entries (348); `coerce` and the `coercible-*` forms (355);
`unique` (370); a non-erased match on a `newtype` (390); `Placed` (397); `World`, `Request`, `Program`,
and `world-do` (408); macros, `Raw`, and handles (418); arrays and `Bytes` as models (449); `Matchable`
types and `matchable-of` (453); run position (456); `comptime-match` (466); `open-adt` and `open-absurd`
(471); `union` and `newtype` (487); `delegate` (492); `Delegate`, `delegate-of`, `coercible-of` (507);
`tail` and `notail` (520); `def-opaque` and `def-prim` (529); slots and `at` (537); at-functions and
at-matches (582); cells (594); `else` (614); `_` as a `def-fns` level (623); `_` as a match annotation
(624); inferred decrease annotations (630); `level-of` (641). It also has `Type : Type` and no positivity
check: `[QUOTE lean/README.md:96-99]` "The fragment has `Type : Type` and datatypes with no positivity
requirement (DESIGN.md §10). The checker types `Type` as `Type` (`TmTy.univ`) and has no positivity check,
so every theorem below covers programs that use both." (`[READ Typing.lean:342]` `| univ : TmTy Γ .univ
.univ`.)

**Left out, in the documents' own words.**

- `[QUOTE lean/README.md:235-236]` "These forms are refused as not supported: every form not named in this
  file."
- `[QUOTE lean/README.md:239-241]` "The mark is recorded and changes nothing else: the runner has no FFI,
  and runs each `extern` function's model, or native code proved to agree with it (above)."
- `[QUOTE lean/README.md:447-448]` "Not supported: `read-file`, `mint-settled-erased`, `settled-mult` and
  `settled-value` outside a macro's function, and positions."
- `[QUOTE lean/README.md:575-581]` "`at` changes no value: the runner computes an `at` result like any
  other. Not done: the slot a forcing unification gives otherwise than through the core's own rules, an
  `at` naming an entry of an enclosing telescope that is not a slot, `_` for an argument whose slot is
  named (its slot is `_` too), and `prove-predates` on a slot first needed after the level other than
  through such a `slot-of`."
- `[QUOTE lean/README.md:591-593]` "A skipped call and an at-match run like any other. A non-erased match
  on a union with several real branches is refused even as an at-match."
- `[QUOTE lean/README.md:595-597]` "a declared opaque type of one `(Slot)` parameter per non-erased field,
  made when first named; a newtype's, an extern type's and a phantom constructor are refused."
- `[QUOTE lean/README.md:611-613]` "Skipping what costs nothing (at-function calls, at-matches, `at`
  entries) is not done (HANDOFF.md)."
- `[QUOTE lean/HANDOFF.md:16-18]` "The runner does not implement `cell-same`, so the prelude leaves out
  `nat-same` and the other functions DESIGN.md section 42 builds on it (item 9)."
- `[QUOTE lean/HANDOFF.md:71-72]` "Arrays, `Bytes` and `Placed` come after cells, `at`, slots and
  at-functions." (This is the plan for the machine run. Today arrays are run through their source models,
  `[READ lean/README.md:449-452]`.)
- Under `[QUOTE lean/HANDOFF.md:83]` "Not done, on this session's reading:" stand three items: item 1 is
  "Slots mean words" (quoted in finding 2); `[QUOTE lean/HANDOFF.md:92-93]` "2. An at-function's body and
  an at-match's branches erasing to nothing, checked in the core rather than the elaborator alone.";
  `[QUOTE lean/HANDOFF.md:94]` "3. A `def-unique` consuming what it captures, checked in the core."

**Forms of DESIGN.md with no trace in the Lean reader.**
`[RAN] grep -c -e K lean/Minimal/Reader.lean` for each K printed 0 for `fn-same`, `cell-same`, `slot-tag`,
`native-compute`, `coercible-tag`, `"imm"`, `"goal"`, `"qed"`, `settled-ty-apply`, `slots-find`. `slot-eq`
has 3 hits, all the reader's internal helper spelled `" slot-eq"` with a leading space, which emits
`Prim.atomEq` for `slot-self` `[READ Reader.lean:2126-2138]`; the §67 primitive `slot-eq` is not in
`lean/prelude.sl` (`[RAN] grep -c slot-eq lean/prelude.sl` printed 0; `lib/prelude.sl` has 2).

**Untrusted, by the README's own list** (three items):
- `[QUOTE lean/README.md:215-216]` "The reader and the elaborator, from surface syntax to `Core`. The
  theorems are about `Core` programs."
- `[QUOTE lean/README.md:217]` "The driver of a `Program` (`Prog.drive`, `Prog.perform`)." with
  `[QUOTE lean/README.md:220-222]` "That this is the run the theorems describe, for the oracle made of
  the answers it gave, is a session's reading, not a proof."
- `[QUOTE lean/README.md:227-229]` "That `Core`, `TmTy`, `CoreTy` and `eval` match MINIMAL.md. That
  agreement rests on reading alone, and the differences below are the ones known."

**How large "large" is.**
- `[QUOTE lean/HANDOFF.md:13-16]` "At the last full run 421 tests were accepted with OCaml's value, 531
  refusals agreed, and 19 + 59 were refused as unsupported; 7 tests OCaml accepts are refused, and one test
  OCaml refuses is accepted (`macro_mint_numeral_of_bad.sl`, item 9)." `tests/` holds 1,337 `.sl` files
  today (`[RAN] ls tests/*.sl | wc -l`); `compare.sh` skips tests with `; stdin`, `; args`, `; env`,
  `; externs`, or `; confine` lines `[READ lean/compare.sh]`. Whether those counts are current is
  `[UNKNOWN]`.
- `lean/prelude.sl` is `lib/prelude.sl` filtered to what the runner accepts `[READ lean/prelude.py]`.
  Counting parenthesised top-level forms with a small script: `lib/prelude.sl` 358, `lean/prelude.sl` 228,
  `lean/prelude-full.sl` 204 `[RAN, python script in my shell; output "top-level forms: 358 / 228 / 204"]`.
  Whether `lean/prelude.sl` was regenerated from today's `lib/prelude.sl` is `[UNKNOWN]`.
- The full run cannot run the whole prelude: `[QUOTE lean/README.md:82-85]` "`prelude-full.sl`: those of
  them on which the full evaluator still finishes, for the runs that use it; `u62-modulus` is `2^62` in
  unary, which only the stripped run leaves uncomputed, so it and everything over `U62` are not there."

---

## 2. The main theorems: exact statements and what they quantify over

All statements are about a `Prog`, a record of ADT declarations, function groups, one main `Core` term, and
an oracle `ask` `[READ Syntax.lean:429-440]`. `Core` is the elaborator's output, not source text
`[READ Syntax.lean:310-323]`.

### 2.1 `eval` and its totality

`[QUOTE lean/Minimal/Eval.lean:64-76]`
```lean
def eval (P : Prog) (μ : Option (List Nat)) (ρ : List Tm) (cnt : Nat) : Core → Except String (List Tm × Nat)
  | .ret ts => .ok (ts.toList.map (·.subst (Tm.env ρ)), cnt)
  | .call f _ args _ _ _ rest =>
    match callee P (f.subst (Tm.env ρ)) with
    | some (env, n, gid, G, F) =>
      let argv := args.toList.map (·.subst (Tm.env ρ))
      let μ' := some (n :: (markedArgs F.tele (.ofList argv)).map Tm.size)
      if h : muLt P.k μ' μ then
        match eval P μ' (env ++ closures env gid G ++ argv) cnt F.body with
        | .ok (outs, cnt) => eval P μ (ρ ++ outs) cnt rest
        | .error e => .error e
      else .error "call does not decrease"
    | none => .error "callee is not a function"
```
`[QUOTE lean/Minimal/Eval.lean:110-115]`
```lean
termination_by c => ((⟨μ⟩ : Mu P.k), sizeOf c)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ h
    | (apply Prod.Lex.right; simp; try omega)
  all_goals (have := sizeOf_selectBr hb; simp; omega)
```
In plain words `[READ Eval.lean:7-41, 64-115]`:

- The measure is a lexicographic pair. First, `μ : Option (List Nat)`: `none` at the top level, above every
  `some`; inside a function `some (n :: sizes)`, where `n` is the level *number* of the callee's group, read
  from the closure's environment, and `sizes` are `Tm.size` of the values of its `subterm`-marked
  arguments. Lists are compared by `lexLt (k + 1)` over the first `P.k + 1` places, a missing place read as
  0. Second, `sizeOf c`, the size of the core term still to run.
- A call into a callee's body strictly lowers the first component, *because the evaluator checks it at run
  time* (`if h : muLt P.k μ' μ`) and returns `.error "call does not decrease"` otherwise. Every other
  recursive call keeps `μ` and runs a strictly smaller core term.
- Levels are numbers from a counter `cnt` that each `def-lvl` run increments `[READ Eval.lean:89]`
  (`| .defLvl rest => eval P μ (ρ ++ [.lvl cnt]) (cnt + 1) rest`).
- Erased code runs: the `.call` case ignores the erasure flag `[READ Eval.lean:66]`.
- So the totality claim is: Lean accepted this definition, for every `Prog`, checked or not. On an
  unchecked program it may answer `.error`. The README says the same: `[QUOTE lean/README.md:101-104]`
  "**`eval` is total, with no fuel.** It is a Lean definition by well-founded recursion, not `partial`, so
  Lean's kernel has checked that it ends on every input, checked or not." The recorded expected output
  shows the check firing: `[RAN] grep -n paradox lean/examples/expected.txt` includes
  `unchecked examples/paradox_curry_bad.sl: stuck: call does not decrease`.
- The run-time check uses sizes, not the strict-subtree order: `[QUOTE lean/README.md:756-758]` "The
  runtime check compares sizes of values where SOUNDNESS.md uses the strict-subtree order. The proof uses
  only that a strict subtree is smaller."

### 2.2 `checked_runs`

`[QUOTE lean/Minimal/Check.lean:32-33]`
```lean
def Checked (P : Prog) (rets : Tm) : Prop :=
  ProgOK P ∧ CoreTy P P.groups.length {tys := #[]} P.main rets ∧ rets.static 0 0
```
`[QUOTE lean/Minimal/Sound.lean:4027-4029]`
```lean
theorem checked_runs (hO : P.OracleOK) {rets : Tm} (h : Checked P rets) :
    ∃ vs cnt, eval P none [] 0 P.main = .ok (vs, cnt) ∧ VTys P (.ofList vs) rets .nil ∧
      ∃ vsS, RunS P [] P.main vsS ∧ Reals P (.ofList vsS) (.ofList vs) rets
```
Plain words `[READ those lines; Check.lean:19-30; Sound.lean:32-66; Strip.lean:134-152]`: for every
program `P` whose oracle is well behaved (`OracleOK`) and whose declarations are well formed (`ProgOK`),
and every closed result telescope `rets` at which `P.main` has a typing derivation from the empty
context: the full evaluator, from the empty environment, counter 0, and the
top-level measure, answers `.ok`; its values have the types `rets` (`VTys`); and a stripped run exists
whose results stand for the full results at the non-erased places (`Reals`). It quantifies over `Core`
programs, not source files. It does not say the fuelled executable `runS` finds that stripped run (2.6).
One documented hole: `[QUOTE lean/README.md:352-354]` "Where the checker cannot build that telescope, the
result is checked as a result of any type (`ArgsTy.anyCons`), and `checked_runs` says nothing of its type."

### 2.3 `no_false`

`[QUOTE lean/Minimal/Sound.lean:4040-4042]`
```lean
theorem no_false (hO : P.OracleOK) {d : Nat} {D : Adt} {args ls : Tm} {m e : Bool} (hD : P.adts[d]? = some D) (hempty : D.ctors = [])
    (hco : D.coercible = false) (hop : D.opq = false) :
    ¬ Checked P (.bind (.ty m e u) (.app (.tyc d ls) args) .nil)
```
Plain words `[READ]`: for every program with a well-behaved oracle and every declared type `d` with no
constructors that is neither of the `Coercible` kind nor opaque, the program is not `Checked` at the
one-entry result telescope of type `(d ...)`, whatever the entry's marks. It is a corollary of
`checked_runs` `[READ Sound.lean:4043-4047]`. It is about a single final result of the main term.

### 2.4 `eval_sound`

`[QUOTE lean/Minimal/Sound.lean:3708-3710]`
```lean
theorem eval_sound (hP : ProgOK P) (hO : P.OracleOK) : ∀ μ ρ cnt c, ∀ b Γ rets, CoreTy P b Γ c rets → EnvOK P ρ Γ →
    LvlBound ρ cnt → MuOK μ Γ ρ → rets.static Γ.n 0 →
    Result P ρ cnt rets (eval P μ ρ cnt c) ∧ Sim P Γ ρ c rets (eval P μ ρ cnt c)
```
`[QUOTE lean/Minimal/Sound.lean:3142-3144]`
```lean
def Sim (P : Prog) (Γ : Ctx) (ρ : List Tm) (c : Core) (rets : Tm) (r : Except String (List Tm × Nat)) : Prop :=
  Γ.ghost = false → ∀ ρS, SimEnv P Γ.er ρS ρ → ∀ vs cnt', r = .ok (vs, cnt') →
    ∃ vsS, RunS P ρS c vsS ∧ Reals P (.ofList vsS) (.ofList vs) rets
```
`[QUOTE lean/Minimal/Sound.lean:1090-1092]`
```lean
def Result (P : Prog) (ρ : List Tm) (cnt : Nat) (rets : Tm) (r : Except String (List Tm × Nat)) : Prop :=
  ∃ vs cnt', r = .ok (vs, cnt') ∧ VTys P (.ofList vs) (rets.subst (Tm.env ρ)) .nil ∧
    LvlBound vs cnt' ∧ cnt ≤ cnt' ∧ ∀ v ∈ vs, v.lc 0
```
Plain words `[READ those lines; Sound.lean:60-65, 510-511, 562, 1002-1005]`: for every measure, environment,
level counter, core term, context, and result telescope, if the term is typed in the context
(`CoreTy`), the environment satisfies the context (`EnvOK`: each value has its entry's type, values are
closed, the fact table's rules hold of the values (`Sat`), each minted level is a number above every level
in the entries before it, the checker's known values stand for the real ones (`FixOK`), delegate pairs
agree (`DeleOK`)), the counter bounds every level in scope, and `μ` is the current function's measure, then
(a) `eval` answers `.ok` with well-typed values, and (b) outside erased code, from any stripped environment
standing for the full one, a stripped run exists whose results stand for the full results. The proof is by
the functional induction of `eval` itself (`induction μ, ρ, cnt, c using eval.induct P`)
`[READ Sound.lean:3711-3712]`.

### 2.5 `machine_main` (file `lean/Minimal/MachineAsm.lean`)

`[QUOTE lean/Minimal/MachineAsm.lean:1824-1830]`
```lean
theorem machine_main (hP : ProgOK P) (hO : P.OracleOK)
    {rets : Tm} {h} (hck : checkCore P P.groups.length {tys := #[]} P.main (.inr 0) = .ok ⟨rets, h⟩)
    (hus : P.usesOK rets = true) {vs : List Tm} {cnt : Nat} (hev : eval P none [] 0 P.main = .ok (vs, cnt))
    {vsS : List Tm} (hrun : RunS P [] P.main vsS) :
    ∃ U K H' vsM, usesCore P P.groups.length {Γ := {tys := #[]}} [] rets P.main = some (U, K) ∧
      RunM P {} [] none P.main H' vsM ∧
      MOut P U 0 ({tys := #[]} : Ctx).er {} [] [] [] (fun _ => False) (fun _ => False) rets [] H' vsM vsS vs
```
Plain words `[READ those lines; MachineSound.lean:950-966; Machine.lean:133-148]`:

- Hypotheses: the checker *function* succeeded on the main term (an equation about `checkCore`, not an
  arbitrary typing derivation); the uses pass `usesCore` succeeded (`usesOK`); a successful full
  evaluation; and a stripped run. The last two are what `checked_runs` concludes, so I take them to be
  dischargeable from it `[INFERENCE]`.
- Conclusion: a machine run from the empty heap `{}` exists, ending in some heap `H'` with results `vsM`,
  and `MOut` holds. At this top-level instance the list saying which results are unique (`ru`) is `[]` and
  the start heap is empty. So, as I read the fields of `MOut`, what it yields here is: the final heap is
  well formed (`wf`), there are as many machine results as stripped ones (`len`), and each non-erased
  machine result decodes in `H'` to the stripped result (`dec`, through `MDec`); `next`, `blk`, `keep`, and
  `foot` hold trivially from an empty start heap `[INFERENCE from MachineSound.lean:950-959]`. The clauses
  about the blocks a `unique` result owns (`uspine`, `uwo`, `usep`) each require `ru.getD k false = true`,
  which is false for `ru = []` `[READ MachineSound.lean:960-966]`, so at the top level they say nothing
  `[INFERENCE from that READ]`. They matter inside the induction (`MRun`,
  `[READ MachineRun.lean:504-507]`).
- Direction: stripped run implies a machine run exists and agrees. There is no converse, and no
  determinism theorem for `RunM` (`[RAN] grep -n "RunM.det\|theorem RunM" -r lean/Minimal` printed
  nothing). Its rules look functional, so it is probably deterministic `[INFERENCE]`.
- The proof is again by induction on `eval`, not on `RunS` `[READ MachineAsm.lean:1744-1747]`, for the
  reason in 7(a) item 6.

### 2.6 The other highlighted statements, and where fuel is

- `[QUOTE lean/Minimal/Strip.lean:106]` `theorem RunS.det {ρ : List Tm} {c : Core} {a b : List Tm} (h1 :
  RunS P ρ c a) (h2 : RunS P ρ c b) : a = b`: a stripped run has one outcome.
- `[QUOTE lean/Minimal/Native.lean:1823]` `theorem runS_sound : ∀ fuel ρ c out, runS P fuel ρ c = some out →
  RunS P ρ c out`: what the fuelled executable returns is a stripped run. There is no completeness
  statement saying that enough fuel finds the run: the only theorems that mention `runS` are `runS_sound`,
  `runS_det`, `runA_eq`, and `runA_toArray` (`[RAN] grep -n "theorem.*runS" lean/Minimal/*.lean` printed
  those four; `grep -n "∃ fuel\|∃ n, runS" lean/Minimal/*.lean` printed nothing).
- The checker returns derivations: `[QUOTE lean/README.md:65-67]` "`Minimal/Check.lean`: the checker. Each
  of its functions returns a typing derivation, so the checker needs no correctness proof of its own."
  `[READ Check.lean:38, 648-649, 929]` (`checkTm' ... : (t : Tm) → Res {T // TmTy P Γ t T}`, `checkProg :
  Res {R // Checked P R}`, with `Res α := Except String α`). A refusal is a string: there is no relation of
  failure and no completeness theorem (`[RAN] grep -rn "Fails" lean/Minimal` printed nothing).
- The world: `[QUOTE lean/README.md:194-196]` "The theorems say nothing about any particular oracle; the
  runner's is the untrusted driver below."

**Where fuel is.** `[RAN] grep -rn "fuel\|Fuel" lean --include='*.lean'` printed 54 lines, in `Native`
(28), `Typing` (9), `Infer` (7), `Syntax` (4), `Reader` (3), and `Run` (3); and, run in `lean/`,
`[RAN] grep -n "runA \|runAM \|runA P\|runS P\|runS (" Minimal/Reader.lean Minimal/Run.lean
Minimal/Infer.lean Minimal/Check.lean Minimal/Typing.lean Minimal/Uses.lean` printed the calls of the
fuelled runners outside the proofs (Reader.lean:992, 1477, 1916, 1938; Run.lean:186, 242, 243;
Typing.lean:177, 184, 186). I then read each:

| Where | Fuel | Evidence |
|---|---|---|
| `eval` (full run) | none; WF recursion plus dynamic check | `[READ Eval.lean:64-115]` |
| `RunS`, `RunM` | none; they are relations, existence proved from `eval` | `[READ Strip.lean:84-103; Machine.lean:97-126]` |
| `runS`, `runAM`, `runA` (what the runner executes) | a `Nat` argument, one unit per recursive call | `[READ Native.lean:1781-1783, 1934-1938, 1986-1987]` |
| the checker's compile-time values (`stepS`, used by `Ctx.adv` inside `CoreTy`) | `opaque fixFuel : Nat := 1000000000` | `[READ Typing.lean:169-196, 545, 553, 561]` |
| the reader's run-position runs and macro expansions | `10000000`, and at most 10000 expansions | `[READ Reader.lean:984, 993, 1477, 1916, 1938]` |
| the runner and the `Program` driver | `100000000`; `Prog.drive` is a `partial def` in `IO` | `[READ Run.lean:178-190, 242-246]` |
| declaration isomorphism, meta solving, a free-variable closure, a numeral-spelling helper | `isoFuel`, or a `fuel` argument | `[READ Typing.lean:268-282; Infer.lean:93-98, 164-168; Reader.lean:1608-1615]` |

So the typing *relation* itself mentions a fuelled function: `CoreTy`'s premises advance the context with
`Ctx.adv P Γ ... `, which calls `stepS`, which calls `runA P fixFuel` `[READ Typing.lean:171-196, 545]`.
When fuel runs out, the checker simply records no known value `[READ Typing.lean:192-196]`.

### 2.7 Why the fuel-free `eval` does not transfer to Sleight, and what does

- `[INFERENCE]` Lean turns a `termination_by` definition into recursion on accessibility of a well-founded
  relation; the relation here is proved well founded for every `k` by induction on `k`
  (`lexLt_wf`, `[READ Eval.lean:11-21]`). This is general knowledge of Lean 4, not something I checked here.
- The order has `P.k + 1` lexicographic places plus the code position, and `P.k` is a property of the
  *object* program `[READ Eval.lean:71, 110; Syntax.lean:475-476]`.
- A session-written README records: `[QUOTE README.md:113-119]` "The author asserts that each Sleight
  function terminates by a lexicographic order of type about ω^(k+2), on the level, the `subterm`
  arguments, and the position in the function body, where k is the largest number of `subterm` parameters
  on any function in the program. Correspondingly, the language as a whole computes exactly the multiply
  recursive functions, so its strength is about IΣ₂ (anticlassicality aside), with proof-theoretic ordinal
  ω^ω^ω, well below Peano arithmetic."
- `[INFERENCE]` If that assertion holds, one Sleight function cannot be a total evaluator for all Sleight
  programs: its own `k` is fixed by its text, while it would have to follow orders of every length. The
  handoff records the owner naming an obstacle of this kind: `[QUOTE scratchpad/handoff.md:19]` "for
  consistency, proving properties about the language runs into a diagonalization argument". It could be
  tested only negatively (try to write it); I did not.
- `[INFERENCE]` The dynamic decrease check is tied to the *full* run: it needs level numbers and the sizes
  of `subterm` arguments, which are erased in the run DESIGN.md describes
  (`[QUOTE DESIGN.md:1279-1280, §29]` "its value was never computed, because the erased positions are
  stripped before the evaluator runs"). A stripped evaluator has nothing to check.
- What Sleight does offer, per DESIGN.md: `[QUOTE DESIGN.md:864-865, §21]` "Subterm recursion (§17) may go
  through an erased field." and `[QUOTE DESIGN.md:1993-1994, §42]` "It never recurses, so an unbounded
  interaction is the driver's loop over total functions."
- `[RAN]` An existing test loops 131,071 times on an erased decreasing argument:
  `./_build/default/bin/main.exe tests/comptime_tail.sl` printed `(Odd)` in 0.93 s (plus one warning).
- `[RAN]` I wrote
  `/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/A4/halts.sl`
  (23 lines): a toy machine whose states are `Nat`s (`(Succ m)` steps to `m`, `(Zero)` is final), a
  relation `(Halts n)` with every field erased, a function `run : (many (Nat) n) (subterm erased (Halts n)
  h) -> (many (Nat) steps)` that recurses on the erased derivation, and an `erased` function `halts-all`
  that builds the derivation for any `n`. `/home/user/sleight/_build/default/bin/main.exe halts.sl` printed
  `3` (plus two style warnings, exit 0); `/home/user/sleight/_build/release/slc --interpret halts.sl`
  printed `3` (same warnings, exit 0). So the Sleight counterpart of Lean's step from "a run derivation
  exists" to "the run ends" is a function that is structurally recursive on an erased derivation of the
  run relation `[INFERENCE from that RAN; shown only for this toy]`. Where no derivation can be produced
  inside the language (which I expect for a full self-evaluator, by the previous point), what is left is a
  total step function looped by the driver, or a hypothesis `[INFERENCE]`.

---

## 3. The run semantics

### 3.1 One syntactic sort for terms, types, values, and words

`[READ lean/Minimal/Syntax.lean:18-41]` The constructors of `Tm` are `fv`, `bv`, `nil`, `cons`, `bind`,
`app`, `tyc`, `vc`, `tyCtor`, `valCtor`, `univ`, `level`, `predates`, `subterm`, `fn`, `mtbl`, then the
run-time ones `lvl (n : Nat)`, `tok`, `clo (env : Tm) (gid j : Nat)`, `nat (n : Nat)`, `ptr (a : Nat)`,
`wld (k : Nat)`. The README: `[QUOTE lean/README.md:54-55]` "`Minimal/Syntax.lean`: terms (`Tm`, the type
grammar of DESIGN.md section 9 with values and closures added), core programs (`Core`)."

- Full-run values: constructor applications holding *all* fields, closures holding their whole environment,
  level numbers, `tok` for proofs, types as values, worlds `[READ Eval.lean:43-53, 64-115]`.
- Stripped values: the same sort, with erased constructor fields masked to `tok`, a newtype value held as
  its field, the prelude's `Nat` as `nat n`, and a delegate bound to its target's value
  `[READ Strip.lean:5-80]`.
- Machine words: the same sort again, with `ptr a` for a block `[READ Machine.lean:19-65]`.

### 3.2 The full and stripped runs are pure and environment-based

Both carry an environment `ρ : List Tm` that only grows by appending, and instantiate terms by
substituting environment values (`·.subst (Tm.env ρ)`, `P.sub ρ`); neither has a heap
`[READ Eval.lean:64-109; Strip.lean:84-103]`. The stripped run has no decrease check
`[READ Strip.lean:87-89]`. A stripped value "stands for" a full one through `Real`
`[READ Strip.lean:134-152]`.

### 3.3 The machine: heap, addresses, blocks

`[QUOTE lean/Minimal/Machine.lean:5-15]`
```lean
abbrev Blk := Nat × Nat × List Tm

structure Heap where
  blk : Nat → Option Blk := fun _ => none
  next : Nat := 0

def Heap.alloc (H : Heap) (b : Blk) : Heap × Nat :=
  ({ blk := fun a => if a = H.next then some b else H.blk a, next := H.next + 1 }, H.next)

def Heap.write (H : Heap) (a : Nat) (b : Blk) : Heap :=
  { H with blk := fun x => if x = a then some b else H.blk x }
```
`[READ Machine.lean:5-65, 97-126, 198-203; MachineSound.lean:946-961]`:

- **Addresses are natural numbers handed out by a bump counter**: allocation returns `H.next` and
  increments it. The invariants use the order: `Heap.WF` (nothing at or above `next`), and "new block" is
  written `H.next ≤ b` in `MOut.foot` and `MOut.uspine`. This is the concrete "newest is largest" model the
  handoff says the owner questioned `[QUOTE scratchpad/handoff.md:36]` "The owner had questioned whether
  the session was assuming a concrete model such as newest or largest address".
- **A block is `(type index, constructor index, field words)`.** Erased fields stay in the block as `tok`
  (`maskArgs`), every block carries its constructor index, and a constructor application with no fields is
  still allocated: `Prog.place` allocates for any `.app (.vc d c _) fs`, and the reader elaborates `(C
  args)` to that shape `[READ Machine.lean:19-34; Strip.lean:29-31; Reader.lean:2376-2386]`. The exceptions
  are the prelude's `Nat` (a number) and a newtype wrapper (its field) `[READ Machine.lean:29-32]`.
- **Closures are not heap objects**: a machine closure is `clo env gid j` with its environment inline
  `[READ Machine.lean:123-124, 136-137]`.
- **Nothing is freed**: the heap has `alloc` and `write` only `[READ Machine.lean:7-15]`.
- **The run is big-step**: `RunM : Heap → List Tm → Pend → Core → Heap → List Tm → Prop`
  `[READ Machine.lean:97]`.
- So the machine is "a heap with in-place update", not the representation of §33. None of §33's statements
  about immediates, tags, hollow types, `vacant-slot`'s word, erased fields occupying no space, or a
  delegate's pointer being its callee's pointer is modelled at the word level `[INFERENCE from those READs
  against DESIGN.md:1459-1491]`.

### 3.4 How slots, cells, `at`, and in-place updates are modelled

| DESIGN.md | Lean model | Evidence |
|---|---|---|
| A slot's run-time value is a word: `[QUOTE DESIGN.md:1803, §38]` "At runtime, the value of a slot is a word, either a pointer or an immediate."; and of `(slot-of x)`: `[QUOTE DESIGN.md:1575, §35]` "Its word is the word of `x`" | A slot is an entry of a one-constructor type; its value is that constructor in every run, also for a non-erased `(slot-of x)` | `[QUOTE lean/README.md:539-541]` "In the core a slot is an entry of type `(Slot)`, made by `Prim.atom`, which evaluates to the constructor"; `[QUOTE lean/README.md:564-566]` "A non-erased slot entry is made `unique` (its value is an immediate, which owns nothing), so `(slot-of x)` may stand at a unique position"; `[READ Eval.lean:47]` (the `.atom d` case returns `.app (.vc d 0 .nil) .nil`) |
| Which entry has which slot is a fact of the fact table (§35) | The link is kept in the reader's state; in the core a telescope gets hidden erased slot entries | `[QUOTE lean/HANDOFF.md:32-33]` "the link from an entry to its slot lives in the reader's state, which inference does not see."; `[QUOTE lean/README.md:549-553]` "A telescope entry written `at v`, or whose slot a `slot-of` or an `at` of the same telescope names, is preceded in the core by a hidden erased entry (`Tm.fn`'s mask): its slot, a `(Slot)` entry, or for `at v` an `is` entry that it is `v`'s slot." |
| Slot equality is forced like any fact (§35, §36) | `Prim.atomEq` gives `Eq` between any two entries of a one-value type; the reader emits it for `slot-self`, for the fresh copy it makes for a non-erased `slot-of`, and for `placed-slot` `[READ Reader.lean:764-766, 2126-2138, 2336-2345, 2945]` | `[QUOTE lean/README.md:571-575]` "as an erased `let-match` on `Refl` of a proof of `Eq (Slot) s σ` (`Prim.atomEq`, which the checker accepts between two entries of a type with one constructor and no fields, all of whose values are that constructor)"; `[READ Typing.lean:421-424; Sound.lean:1741-1753]`; `[RAN] grep -n atomEq lean/Minimal/Reader.lean` printed lines 2138 and 2345 |
| `at`: `[QUOTE DESIGN.md:1649-1650, §36]` "An entry written `at`, whether a parameter, a return or an annotation entry, is omitted after erasure: its word is the word of whatever it is `at`." | Computed and passed like any value | `[QUOTE lean/README.md:575-576]` "`at` changes no value: the runner computes an `at` result like any other." |
| A cell is memory with slots (§37) | A cell is an axiom of an opaque type; `tok` in the full and stripped runs; in the machine, the pointer of the destructured block or of a fresh empty block `(0, 0, [])` | `[QUOTE lean/README.md:597-600]` "A cell is an axiom of its type (`Prim.axm`, which the checker accepts at a non-erased position too, since any value inhabits an opaque type), and holds nothing."; `[READ Machine.lean:89-95]` |
| `cell-write` at `unique`: `[QUOTE DESIGN.md:1754-1755, §37]` "This is a physical store into memory that the cell's eventual invocation re-creates; it does no usage accounting of its own." | No store: the pending mark `.write true` makes the following `Prim.axm` return the entry's pointer | `[READ Machine.lean:92-94]`; `[RAN] grep -n "\.write\b\|Heap.write" lean/Minimal/Machine.lean` shows `H.write` only at line 78, inside `Prog.reuse` |
| Invocation at `unique` creates its value at the cell (§37) | `Prog.reuse` overwrites the whole block with the new constructor and fields, and falls back to allocating when the entry is not a pointer | `[READ Machine.lean:73-81, 90]` |
| `(at)` before an argument skips a store (§37) | Checked statically as a slot equation; the machine still writes every field | `[QUOTE lean/README.md:602-604]` "and `(at)` before an argument, or `(at (u a ...))` for all of them, asks the core that the argument's slot canonicalizes to the cell's"; `[READ Machine.lean:73-81]` |
| `cell-match` reads the words of a cell (§38) | Slots are read from the cell's type | `[QUOTE lean/README.md:600-601]` "`cell-alloc`, `cell-write`, a pattern's cell binder and `cell-match` make cells and read their slots from their types" |
| At-functions and at-matches cost nothing (§39, §40) | Checked by the reader only; they run | `[QUOTE lean/README.md:582-583, 591-592]` "At-functions and at-matches (sections 39 and 40), checked by the elaborator:" / "A skipped call and an at-match run like any other." |
| `unique` (§13, §15) | Checked by the reader, again by a separate Boolean pass `usesCore` over marks the reader leaves; not part of the typing relation | `[QUOTE lean/README.md:766-770]` "`unique` is checked by the elaborator, and again in the core by `usesCore` (`Minimal/Uses.lean`), which the runner requires of a checked program and which reads the marks the elaborator leaves (`Mark.uq`, `Mark.uqScr`, `Mark.rebind`, `Mark.reuse`, `Mark.write`)"; `[READ Uses.lean:175-255; Typing.lean:572]` |

**The marks.** Whether the machine writes in place is requested by a core statement
`.chk (.mark m) a b rest` that the reader emits: `.reuse (pm == .uniq)` before an invocation, `.alloc`
before `cell-alloc`, `.write (md == .uniq)` before `cell-write`, `.cellOf` for a pattern's cell binder
`[READ Reader.lean:1679, 2055, 2073, 2502]`. The machine keeps the mark "pending" for the next statement
`[READ Machine.lean:83-95, 125]`. The full and stripped runs skip marks `[READ Eval.lean:94; Strip.lean:103]`.

**Consequence I draw.** The content of a cell between its allocation or `cell-write` and its invocation is
never observable in the Lean machine, and an `at` promise is never used to fetch a word. So a wrong slot
fact could not make the Lean machine misbehave, which is why its theorems cannot be evidence for slot
soundness (OPEN.md 3) `[INFERENCE from the table]`. Compare the recorded output
`unchecked examples/at_cell_bad.sl: (P 2 1)`: a program the checker refuses for its `at` runs to a value
unchecked `[RAN] grep -n at_cell lean/examples/expected.txt`.

### 3.5 What "running with in-place updates agrees with that" relates

The phrase is the top-level README's: `[QUOTE README.md:67-68]` "and that running with in-place updates
agrees with that (`machine_main`)". The theorem is in `lean/Minimal/MachineAsm.lean:1824`; it relates
`RunM` (Machine.lean) to `RunS` (Strip.lean) through `MDec`, and to the full run's values through the
ownership relations `Spine` and `WO` (section 2.5). The invariant inside the induction is three-way: each
live entry has a machine word, a stripped value, and a full value (`Spine (H : Heap) : Tm → Tm → Tm → Nat →
Prop`, `WO (H : Heap) : Tm → Tm → Tm → Prop`, and `MFrame ... (ρM ρS ρ : List Tm)`)
`[READ Machine.lean:160-196; MachineSound.lean:932-948]`.

### 3.6 Is the primary semantics pure, with the machine proved afterwards? Yes.

- `[QUOTE lean/HANDOFF.md:58-61]` "The owner's goal, given in chat: a run stripped not only of erased code
  but of everything the language says costs nothing at run time, proved to end in the same values as
  `RunS`, and so, through `eval_sound`, as the full run. That is OPEN.md 2's first step." (A session's
  record of a chat; I cannot verify it.)
- `[QUOTE lean/HANDOFF.md:74-78]` "`Minimal/Machine.lean`'s `RunM` does the third and fourth items: a heap,
  cell invocations at unique written in place (`Prog.reuse`), `cell-alloc` allocating, and a call building
  only its non-erased arguments. `at` entries, skipped calls and slots are not treated specially yet."
- The git history cannot date this: the clone is shallow (`[RAN] git rev-parse --is-shallow-repository`
  printed `true`; `git log --oneline -- lean/ | wc -l` printed 3).

### 3.7 Every piece of evidence I found about why the pure-first route was costly

No document says outright that the route was a mistake. `[RAN] grep -n -i
"rewrit\|painful\|mistake\|regret\|redo\|start over\|from scratch\|hard to\|difficult" lean/*.md` found only
"may be mistaken" (twice) and `regen.sh`'s "rewrite examples/expected.txt". The judgement on rewriting
reaches me only through the handoff: `[QUOTE scratchpad/handoff.md:23]` "That work reached a point where
the Lean code might be worth rewriting, in particular in how it deals with slots and mutation." What the
documents do contain:

1. Slots as locations were left for last and remain undone: `[QUOTE lean/HANDOFF.md:85-91]` "Slots mean
   words: every slot fact the checker holds (`at` promises, forcings, `slot-self`, the writers of DESIGN.md
   section 36) is true of the words, or reading an `at` entry back from its target gives the wrong value.
   That is OPEN.md 3, which the owner believes holds; forcing through a type indexed by `(Slot)` is the case
   it names. The owner confirmed in chat that this lemma is part of the task. Should it need the checker
   tightened, that is the owner's to decide."
2. Adding locations is not incremental: `[QUOTE lean/HANDOFF.md:399-407]` "Deferred by the owner:
   `cell-same` (DESIGN.md section 68). Its `EONonErased` carries a `JMEq` of two cells from their slots
   being equal, and the core here knows nothing of locations (two slots are one only when they canonicalize
   to one entry), so the checker has no rule giving that equality. A session's reading is that supporting
   it would mean the proofs tracking slots as locations (live cells whose slot entries canonicalize to one
   entry being equal values), not a case beside the existing ones. The call's `at` requirement is already
   checked by the core, as for any at-function."
3. The stripped representation blocks a DESIGN.md feature: `[QUOTE lean/HANDOFF.md:23-30]`
   "`at_match_union.sl`: a non-erased at-match on a union newtype with several real branches. The
   reference emits no code for it. Here the reader refuses it, and so does the core checker ("a match with
   an erased discriminant has more than one real branch"): the stripped run holds a newtype's value as its
   field, so nothing chooses the branch. A session's reading is that accepting it needs a new core rule
   (for example, that every real branch strips to the same code) and its proof, which is the owner's to
   decide."
4. Slot bookkeeping outside the core breaks inference: `[QUOTE lean/HANDOFF.md:31-35]` "`at_target_wild.sl`:
   `_` for an argument whose slot a later parameter names; the link from an entry to its slot lives in the
   reader's state, which inference does not see. The slot must also be minted, as a statement before the
   call, before inference has said whose slot it is."
5. The ownership invariant had to mention the full run: `[QUOTE lean/HANDOFF.md:100-102]` "Ownership
   (`Spine`, `WO`) is keyed on the full run's value as well as the stripped one, so that a unique newtype
   wrapper around a shared field (16's `coercible-sym`) owns nothing."
6. The machine proof could not be a simulation from the stripped run alone:
   `[QUOTE lean/HANDOFF.md:324-330]` "The agreement theorem is by the same induction as `eval_sound` (on
   `eval`, under `CoreTy` and `EnvOK`) rather than on `RunS`, because, on this session's reading, at a call
   the caller counts an argument's use by the callee's type as the caller sees it, while the callee's body
   is checked against its own telescope, and only typing (`VTy`) ties the two. It relates machine words to
   the full run's values directly, with an ownership invariant".
7. Typing is not unique, so the machine theorem is about the checker function:
   `[QUOTE lean/HANDOFF.md:254-261]` "The assembly takes the checker's success on a core (`checkCore … =
   .ok …`) as its hypothesis rather than an arbitrary `CoreTy` derivation. On this session's reading typing
   is relational (a primitive's, a callee's or a scrutinee's type is not unique), so the context a `CoreTy`
   derivation gives the rest of a core need not be the one the pass used, while the checker computes those
   types with the same functions as the pass (`checkPrim`, `checkTm`, `checkArgs`, `shapeOf`)."
8. Machine notions leaked back into the pure proof: `Sound.lean` imports `Minimal.Machine`, and the value
   typing of a `Coercible` proof (`VTy.coer`) carries `CoerOwn`, defined with `Twin` and `NoSpine`, which
   quantify over heaps `[READ Sound.lean:6, 24-26, 52-53; Machine.lean:276-279]`.
9. Three runs holding a value differently coarsened I/O: `[QUOTE lean/README.md:658-661]` "The oracle that
   answers a `world-do` is keyed by the world's step number and the request's constructor alone, not the
   request's fields, so that the full run, the stripped run and the machine run, which hold a request
   differently, ask it the same question."
10. The primary semantics cannot run real programs: `[QUOTE lean/HANDOFF.md:370-373]` "**The full evaluator
    on the prelude.** `u62-modulus` is `2^62` in unary, so `prelude-full.sl`, which `--full` and
    `--unchecked` load, leaves out it and everything over `U62`. `prelude.sl` has them, since the stripped
    run never computes it." And `[QUOTE lean/README.md:331-332]` "A numeral that a proof form below names
    goes up to 100000, since its proof is built in unary."
11. Big-step runs cannot state the run-time claims of §19: `[QUOTE lean/TAIL.md:23-26]` "Every run the
    theorems describe is big-step (`eval`, `RunS`, `RunM`). A big-step run has no stack, so, as far as a
    session can tell, "this call reuses its caller's frame" cannot be stated about any of them as they
    are." and `[QUOTE lean/TAIL.md:20-21]` "The marks never reach the core, so no theorem says anything
    about them."
12. The delegate's shared pointer (§33) needed special handling on both sides:
    `[QUOTE lean/README.md:759-765]` "The body of a function with a `delegate` body is checked with every
    entry made before the function's parameters erased except its target, and `delegate-of` names only a
    non-erased function of a non-erased block. Without the first, the proof had no stripped environment
    for the delegate's body when the only stripped value at hand stood for its target; without the second,
    `Real.dele` could not relate a stripped value to the delegate in both directions." (`Deleg.lean` 256
    lines, `MachineDeleg.lean` 392 lines, `[RAN] wc -l`.)

---

## 4. Evaluation order

**The proved semantics has no sibling computations to order.** `Core` is a sequence of statements whose
operands are terms, not computations:
`[QUOTE lean/Minimal/Syntax.lean:310-314]`
```lean
inductive Core where
  | ret (ts : Tm)
  | call (f : Tm) (dec : Dec) (args : Tm) (er : Bool) (ms : List Bool) (ve : Option (List Bool)) (rest : Core)
  | mtch (s : Tm) (rets : Tm) (brs : List (Nat × Nat × Tm × Core)) (els : Option Core) (er : Bool) (rest : Core)
  | prim (p : Prim) (er : Bool) (rest : Core)
```
In `eval`, a call substitutes the environment into `f` and `args`, runs the callee's body, then `rest`; a
`seq` runs `body` then `rest` `[READ Eval.lean:66-76, 106-109]`. In the machine, the allocations of one
term or argument list go left to right, inner blocks first:
`[QUOTE lean/Minimal/Machine.lean:36-41]`
```lean
def Prog.buildArgs (P : Prog) (H : Heap) (f : Nat → Tm) : Tm → Heap × Tm
  | .cons a as =>
    let (H, a') := P.build H f a
    let (H, as') := P.buildArgs H f as
    (H, .cons a' as')
  | t => (H, t.subst f)
```

**The order is fixed by the untrusted reader, which flattens nested forms left to right.**
`[QUOTE lean/Minimal/Reader.lean:2511-2518]`
```lean
  for (e, i) in es1.zipIdx do
    let m := ms.getD i .many
    let exp := match t with | .bind (.ty ..) A _ => some (Tm.bind (.ty false m.isEr false) A .nil) | _ => none
    let (s, r) ← elabExpr sc [m] exp e
    ss := ss ++ s
    ts := ts ++ r
    t := match t, r with | .bind _ _ rest, [a] => rest.inst a 0 | _, _ => .nil
  return (ss, ts)
```
- A call is emitted as the decrease proof's statements, then the arguments' statements in argument order,
  then the call: `[QUOTE lean/Minimal/Reader.lean:2453]` `return (ss0 ++ ss ++ [.call f dec (.ofList ts)
  (!want.isEmpty && want.all (·.isEr)) (want.map (·.isEr)) ve],`.
- A computed head runs before the arguments: `[READ Reader.lean:1873-1877]` (the head's statements `ss`,
  its temporary `ss2`, then the application's `ss3`: `return (ss ++ ss2 ++ ss3, ts)`).
- A `values` is elaborated by the same `elabArgs` `[READ Reader.lean:1945]`; a match's scrutinee statements
  precede the match `[READ Reader.lean:2607, 2623-2624]`.
- So: left to right, each argument's nested work completed before the next begins, head first. That
  coincides with the rule of the handoff's proposal A (`[QUOTE scratchpad/handoff.md:34]` "the
  sub-expressions that run are evaluated left to right, each completely before the next, the head of an
  application first"); in lean/ it is a property of untrusted code that no theorem mentions
  `[INFERENCE from those READs and lean/README.md:215-216]`.

**DESIGN.md.** I found no statement of an order among the sub-expressions of one form.
`[RAN] grep -n -i "left to right\|left-to-right\|order of evaluation\|evaluation order\|evaluated in\|in
order" DESIGN.md` printed seven lines (370, 699, 826, 985, 1163, 1420, 2185), none about evaluating sibling
sub-expressions. The nearest text is `[QUOTE DESIGN.md:655-658, §15]` "Every argument to a constructor, a
function or a cell behaves as if it were first bound to an anonymous variable. An argument that is already
a variable is not rebound. That binding is a statement (§27) placed just before the statement or final
form that contains the call", and `[QUOTE DESIGN.md:1185-1187, §27]` "This nests: the forms inside a form
run before it does, and the statements of a `let`'s right-hand side complete before the enclosing `let`
does." One difference the session records between its reader and the reference:
`[QUOTE lean/HANDOFF.md:478-481]` "`values` in a call's argument position splices its values into the
call's arguments here, so `(nat-add (values 1 2))` gives 3, while the reference refuses it".

---

## 5. Proof-size data

`[RAN] wc -l -c lean/Minimal/*.lean`, plus `grep -c '^theorem '` per file:

| File | Lines | Bytes | Theorems | Role |
|---|---:|---:|---:|---|
| `MachineRun.lean` | 4,238 | 256,463 | 164 | machine agreement, one core form at a time |
| `Sound.lean` | 4,054 | 234,112 | 237 | `eval_sound`, `checked_runs`, `no_false` |
| `Reader.lean` | 3,157 | 163,069 | 0 | reader and elaborator, untrusted |
| `MachineSound.lean` | 2,351 | 138,271 | 103 | machine base lemmas, frames, `MFrame`, `MOut`, `GOK` |
| `Native.lean` | 2,013 | 98,599 | 43 | `runS`, `runAM`, six native externs and their proofs |
| `MachineAsm.lean` | 1,846 | 113,002 | 48 | `machine_sound`, `machine_main` |
| `Check.lean` | 984 | 58,189 | 0 | derivation-returning checker |
| `Typing.lean` | 608 | 34,612 | 3 | typing relations |
| `Syntax.lean` | 536 | 17,154 | 4 | `Tm`, `Core`, `Prog` |
| `Infer.lean` | 452 | 21,331 | 0 | `_` inference, untrusted |
| `MachineDeleg.lean` | 392 | 23,667 | 13 | delegates on the machine |
| `Machine.lean` | 374 | 19,592 | 19 | heap, `RunM`, ownership relations |
| `Run.lean` | 298 | 13,984 | 0 | driver and printer |
| `Uses.lean` | 292 | 12,619 | 0 | `usesCore` |
| `Deleg.lean` | 256 | 13,720 | 21 | delegates in the stripped run |
| `UnifySound.lean` | 210 | 10,251 | 18 | unification soundness |
| `Strip.lean` | 208 | 9,916 | 9 | `RunS`, `Real` |
| `Unify.lean` | 129 | 4,416 | 3 | unification |
| `Eval.lean` | 117 | 4,901 | 2 | `eval` |
| `Lemmas.lean` | 110 | 5,150 | 19 | substitution lemmas |
| **Total** | **22,625** | **1,253,018** | | |

Grouped (`[RAN]`, a Python tally over the same files):

| Group | Lines | Share | Bytes | Share |
|---|---:|---:|---:|---:|
| Machine proofs (`MachineSound`, `MachineRun`, `MachineDeleg`, `MachineAsm`) | 8,827 | 39.0% | 531,403 | 42.4% |
| Full and stripped soundness (`Lemmas`, `UnifySound`, `Sound`, `Deleg`) | 4,630 | 20.5% | 263,233 | 21.0% |
| Untrusted front end (`Reader`, `Infer`, `Run`) | 3,907 | 17.3% | 198,384 | 15.8% |
| Definitions (`Syntax`, `Eval`, `Strip`, `Unify`, `Typing`, `Check`) | 2,582 | 11.4% | 129,188 | 10.3% |
| Native externs (`Native`) | 2,013 | 8.9% | 98,599 | 7.9% |
| Machine definitions (`Machine`, `Uses`) | 666 | 2.9% | 32,211 | 2.6% |

Other measurements:
- The longest single proofs: `eval_sound` 319 lines, `prim_sound` 285, `MSound.call` 274, `MSound.case`
  234, `MFrame.bindR` 205, `MSound.mtch` 200, `usesCore_uq` 197 `[RAN, awk over the files]`.
- The invariants are wide: `MFrame` has 11 fields over three environments (`ρM ρS ρ`) and three address
  sets (`Res Out Shr`), `MOut` 10 fields, `GOK` 6 `[READ MachineSound.lean:932-966, 2338-2349]`.
- Automation: the string `simp` occurs 3,255 times and `omega` 473 times across the sources
  `[RAN] cat lean/Minimal/*.lean | grep -o -e simp | wc -l` (and likewise for `omega`).
- Native arithmetic: six functions (`add`, `nat-cmp`, `mul`, `sub`, `divmod`, `nat-mod`) take most of a
  2,013-line file `[QUOTE lean/README.md:150-151]` "So far that is `add`, `nat-cmp`, `mul`, `sub`,
  `divmod` and `nat-mod` (`Minimal/Native.lean`)."
- For scale, `mini/` (the minimal fragment's relations and deriving functions in Sleight) is 6,849 lines
  of `.sl` plus a 165-line README `[RAN] wc -l mini/*.sl mini/README.md` (total 7,014); the handoff says of
  it `[QUOTE scratchpad/handoff.md:54]` "the preservation argument itself is open".

**What this suggests** `[INFERENCE]`:
- Relating a pure reference run to a mutating machine cost 1.9 times the lines of the entire soundness
  proof, for a machine that mutates in exactly one way and ignores `at`, slots, and representation.
- The session's own estimate for adding a stack is the same again: `[QUOTE lean/TAIL.md:54-57]` "Stage 1
  is small. Stage 2 is a moderate change to the reader plus a proof of agreement with `RunS`. Stages 3 and
  4 are expected to be of the order of the existing machine proofs (`MachineRun.lean`, `MachineAsm.lean`)."
- The cost is driven by the three-way invariant and by proving that mutation is unobservable (ownership,
  frames, closures' captures, delegates, `coerce`), which is an obligation only when the reference run is
  pure. If the spec's run is the mutating machine, an agreement theorem between compiler output and spec
  does not owe that proof.
- Sleight has no `simp` or `omega`. A proof of this shape in Sleight would have to be written out as
  structural recursions, so its size should be expected to be larger, not smaller.

---

## 6. SOUNDNESS.md (a session's argument, not the owner's)

**What it argues.** `[QUOTE SOUNDNESS.md:13-14]` "The claim is relative: **whatever soundness the rest of
the language has, §10 does not take away.**" Its four claims, `[QUOTE SOUNDNESS.md:47-56]`: "**(C) Checking
terminates.** Elaboration of every form ends, apart from a crash of the host (§31)." / "**(T) Totality.**
In the *full semantics* of part 3 below, in which erased code runs too, every function activation returns,
apart from a crash." / "**(S) Safety.** No reachable state of the full semantics reads a word as a field
of a constructor that did not build it, enters a refuted branch, or runs the body of an `absurd`
function." / "**(E) Erasure.** The run the implementations perform, with erased positions stripped,
follows a run of the full semantics, so (S) carries over to it."

**Its full semantics.** `[QUOTE SOUNDNESS.md:113-121]` "Every position runs, erased ones included; a
`Level`, a proof and a type are ordinary values. Each `def-lvl` that runs mints a new level, and levels are
ordered by minting time, a well-order of type ω. - Values are finite trees, and are immutable: a `unique`
binder, a cell and an in-place update are read as an implementation of fresh immutable values. That
reading is OPEN.md 2's first step and OPEN.md 3. For the cells of `lean/`'s fragment, `machine_main`
appears to prove it (part 10); beyond them this note assumes it rather than proves it."

**The invariants it names.** `[QUOTE SOUNDNESS.md:132-141]` "**(I1) Facts are true.** Every `is` fact and
type fact in force holds of the values the entries are bound to, reading a term of §9's grammar as the
tree it builds. - **(I2) `Subterm` is true.** For every `(Subterm A a B b)` token in scope, the value of
`a` is a strict subtree of the value of `b`. - **(I3) `Predates` is true.** For every `(Predates A x L)`
token in scope, every level occurring in the value of `x`, or `x` itself if it is a level, was minted
strictly before the level `L` denotes. - **(I4) No phantom head.** No value bound at a non-erased position
is headed by a phantom constructor (§21)." Plus a lexical-order lemma `[READ SOUNDNESS.md:155-166]`.

- (I1) is the one it does not prove: `[QUOTE SOUNDNESS.md:180-181]` "**Preservation of (I1)** is the
  load-bearing lemma that this note does *not* prove; `lean/` proves it for its fragment (part 10)."
- Mapping to Lean: `[QUOTE SOUNDNESS.md:387-389]` "(I1) is `Sat`, in `EnvOK`; (I2) and (I3) are how `VTy`
  reads `Subterm` and `Predates`; the lexical-order lemma is `Chrono`; part 5's bound k rests on
  `Tm.isTele`." Neither this nor lean/README.md:207-211 names a counterpart of (I4); in the code I see
  non-phantom conditions on `Real.con` and on `rt` `[READ Strip.lean:135; Typing.lean:316-322]`.
- Because every slot is one value in Lean (finding 2), Lean's (I1) says nothing about slot facts
  `[INFERENCE]`. SOUNDNESS.md itself lists slots among "The parts most in need of checking"
  `[QUOTE SOUNDNESS.md:187-189]` "The parts most in need of checking are the `Matchable` invariant of §8,
  the unification of unopened first-class type constructors (§8), and slots (OPEN.md 3)."

**Totality needs the bound k.** `[QUOTE SOUNDNESS.md:253-256]` "The bound k is essential. A call may
decrease its argument at index i and pass anything after i, so with no bound on the number of `subterm`
parameters this chain would go down at every step and never end, each call decreasing a later index than
the one before:". And erasure needs totality: `[QUOTE SOUNDNESS.md:314-316]` "Without (T) this step fails:
a non-terminating erased proof of `False` would be skipped and its claim used, which is the usual way
`Type : Type` turns into unsafety."

**`slot-eq`, `cell-same`, `fn-same`, and the other word comparisons.**
- `[QUOTE SOUNDNESS.md:189-193]` "Also assumed: the FFI agrees with its models (§42), the `Slots` functions
  of §69 included, and `slot-eq`, which §42 exempts from that, answers `Some` only for one word (§67);
  `cell-same` yields its `JMEq` only for equal cells (§68), which rests on OPEN.md 3;"
- `[QUOTE SOUNDNESS.md:202-210]` "**Run-time comparisons yield true equalities.** Forcing treats a
  constructor as injective in every field, erased ones included. That is valid for value trees, but a run
  compares words, and the erased parts of a value leave no trace in its word. So every `Eq` or `JMEq` that
  `slot-eq`, `cell-same`, `fn-same` or a `*-same` function of §42 yields has to hold of the values in the
  full semantics, at least in every part that forcing can tell apart. Two values that differ only in erased
  parts can share a word. For example, every value of a hollow type is at `vacant-slot` (§33)."
- On `fn-same`, two session documents differ in tone. `[QUOTE SOUNDNESS.md:219-223]` "`fn-same` can relate
  two distinct definitions at one word, a `delegate` body and its callee (§33). This appears harmless only
  because §7 gives a declared name no distinctness of its own, and because equal types constrain the
  captured erased values that a type mentions." against `[QUOTE OPEN.md:202-209]` "But its conclusion
  seems false in SOUNDNESS.md's full semantics: two closures at one word can differ in what they capture
  or pass erased. Examples are two `delegate`s to one target with different erased arguments, or a closed
  inner function that extraction allocates once. So (I1) and (I3) would have to read facts at function
  types up to "stands for the same stripped closure", much as `lean/`'s `Real` does, and every form would
  need checking against that reading." DESIGN.md gates the form: `[QUOTE DESIGN.md:3125-3126, §70]` "It is
  available only under `--fn-same` (MANUAL.md); without the flag it is an error."
- None of `slot-eq`, `cell-same`, `fn-same` is in the Lean fragment (section 1).

**Extern models versus FFI implementations.**
- `[QUOTE SOUNDNESS.md:70-80]` "These claims are meant relative to the shipped prelude, `lib/prelude.sl`:
  its extern models and its `def-prim` and `def-opaque` signatures are among the assumptions of parts 4
  and 11. A program run with `--no-prelude` may write its own extern models (§42) and its own `def-prim`
  and `def-opaque` declarations (INTERNALS.md 1, 2). As far as a session has checked, these are then
  trusted axioms that the checker does not verify: a model is checked against the FFI table, keyed by
  name, for non-erased arity and constructor shape only, and a `def-prim` signature not at all. A false
  one can make an accepted program reach an `absurd` body or a refuted branch, so the claims do not cover
  such a program."
- `[QUOTE SOUNDNESS.md:406-411]` "**The FFI implementations.** They are unchecked OCaml.
  `lib/ffi_core.ml` uses unchecked array and string access and `Obj.magic`, relying on the erased proofs
  in the extern signatures. So a false proof that reaches them, through a gap in (E) or a false assumption
  above, can cause an out-of-bounds access or wrapped integer arithmetic, not just a wrong answer."
- DESIGN.md's own requirement: `[QUOTE DESIGN.md:1951-1955, §42]` "An `extern` implementation must agree
  with its model: except through `slot-eq` (§67), running the models instead of the implementations must
  give a program the same values, though not the same cost, and either may crash where the other does not
  (§31)."
- Lean's stance: no FFI; models run; six arithmetic functions run natively, each with a proof against its
  model `[QUOTE lean/README.md:148-150]` "An extern function runs natively only once a Lean proof shows its
  native code agrees with its model; none is trusted unproved."

**Stored values (`comptime-match`, OPEN.md 4).**
- `[QUOTE OPEN.md:38-41]` "Facts from stored values. A `comptime-match` trusts the evaluator (§29). Should
  a reference evaluator inside the checker arbitrate runs that produce facts, so that a wrong evaluation
  cannot produce a `(False)` token through an erased field?"
- `[QUOTE SOUNDNESS.md:403-405]` "**The compile-time evaluator.** It runs run-position forms (§29). The
  facts those forms record are true only if it computes what the full semantics would."
- DESIGN.md says the same of itself: `[QUOTE DESIGN.md:1305-1307, §29]` "Every fact derived from a stored
  value, that is, a `comptime-match` and everything that follows from the fields it binds, relies on the
  evaluator having evaluated correctly."
- In Lean the question is answered by construction for its fragment: the checker's known values
  (`Ctx.fixed`) are computed by the proved stripped runner inside the typing relation, and `EnvOK` carries
  that each stands for the full run's value (`FixOK`); `comptime-match` uses them through
  `BranchOK.fixedOut` `[READ Typing.lean:171-196, 594-596; Sound.lean:21-22, 60-65]`.

---

## 7. Lessons for a from-scratch formalization in Sleight

### (a) Lessons the Lean documents themselves state

Each is a statement by a session about what the proof needed or could not do.

1. **Telescopes must be syntax.** `[QUOTE lean/README.md:744-747]` "A call's `Fn` telescope and a match's
   return telescope must be written out entry by entry, not reached through a variable (`Tm.isTele`).
   Without this check the proof did not go through: a telescope held in a variable can have more entries
   at run time than the checker counted."
2. **Value typing is syntactic.** `[QUOTE lean/README.md:200-205]` "The proof is a syntactic,
   environment-based one. `VTy` says what it is for a value to have a type. It is defined by recursion on
   values, not on types, so neither `Type : Type` nor a type whose constructor takes a function out of the
   type itself gets in the way. This is a session's reading of why the proof goes through, not something
   the Lean files state."
3. **A derivation-returning checker needs no soundness proof of its own.** `[QUOTE lean/README.md:65-67]`
   "Each of its functions returns a typing derivation, so the checker needs no correctness proof of its
   own."
4. **Slots as locations are a different proof, not an added case.** `[QUOTE lean/HANDOFF.md:403-406]`
   "supporting it would mean the proofs tracking slots as locations (live cells whose slot entries
   canonicalize to one entry being equal values), not a case beside the existing ones."
5. **The slot lemma is owed before `at` can be skipped.** `[QUOTE lean/HANDOFF.md:85-88]` "Slots mean
   words: every slot fact the checker holds (`at` promises, forcings, `slot-self`, the writers of DESIGN.md
   section 36) is true of the words, or reading an `at` entry back from its target gives the wrong value."
6. **Uses at a call are tied to the callee only through typing**, so the machine proof ran under typing
   and the full run. `[QUOTE lean/HANDOFF.md:326-328]` "at a call the caller counts an argument's use by
   the callee's type as the caller sees it, while the callee's body is checked against its own telescope,
   and only typing (`VTy`) ties the two." (Full passage in 3.7 item 6.)
7. **A typing relation whose derivations are not unique forces theorems about the checker function.**
   `[QUOTE lean/HANDOFF.md:256-259]` "typing is relational (a primitive's, a callee's or a scrutinee's
   type is not unique), so the context a `CoreTy` derivation gives the rest of a core need not be the one
   the pass used". (Full passage in 3.7 item 7.)
8. **A big-step run cannot carry claims about frames.** `[QUOTE lean/TAIL.md:23]` "Every run the theorems
   describe is big-step (`eval`, `RunS`, `RunM`)." (The sentence that follows it is quoted in 3.7 item
   11.)
9. **Decisions made by scanning names ahead of elaboration go wrong under aliases and macros.**
   `[QUOTE lean/HANDOFF.md:446-451]` "**Decisions the reader makes by name, ahead of elaboration.** A macro
   can rebind a name or produce a form, and an alias can rename a special form, so a decision about what a
   form is belongs where the elaborator handles it, with the scope there. These are still made by scanning
   syntax for names first, and an alias, a shadowing binder or a macro's output can mislead them:"
10. **Tail position needs post-erasure code as an object.** `[QUOTE lean/TAIL.md:34-41]` "**Post-erasure
    code as a type.** An `ECode` (let, call, match, values) and a function from the core to it that drops
    erased statements, types, coercions and placings, resolves renaming `let`s and drops `at` returns, with
    a proof that running `ECode` agrees with `RunS`. Tail position is then defined on `ECode` by section
    19's rules, and a checked function computes it, in place of the reader's syntactic analysis. This alone
    would remove the alias divergence above and make the marks checked rather than trusted." The file
    opens `[QUOTE lean/TAIL.md:3]` "A proposal for the Lean development in `lean/`, not adopted."
11. **Several runs force a coarser world.** `[QUOTE lean/README.md:658-661]` "The oracle that answers a
    `world-do` is keyed by the world's step number and the request's constructor alone, not the request's
    fields, so that the full run, the stripped run and the machine run, which hold a request differently,
    ask it the same question."
12. **A semantics in which erased code runs cannot execute the prelude.** `[QUOTE lean/HANDOFF.md:370-372]`
    "`u62-modulus` is `2^62` in unary, so `prelude-full.sl`, which `--full` and `--unchecked` load, leaves
    out it and everything over `U62`."
13. **Proving a native extern against its model is done one function at a time, and is brittle.**
    `[QUOTE lean/HANDOFF.md:351-354]` "The templates are the prelude's elaborated bodies at their fixed
    places; a change to those prelude forms means regenerating them (a session dumped the groups with a
    small Lean script and pasted them in)."
14. **An empty-type encoding of an opaque type loses a case the design allows.**
    `[QUOTE lean/README.md:655-656]` "The encoding cannot express a macro world that escapes an expansion
    erased, which DESIGN.md section 65 allows."
15. **Erasure safety rests on totality of erased code.** `[QUOTE SOUNDNESS.md:314-316]` "Without (T) this
    step fails: a non-terminating erased proof of `False` would be skipped and its claim used".

### (b) My own inferences (each `[INFERENCE]`, with what it rests on)

1. **Give slots their run-time meaning in the spec's run from the first rule.** DESIGN.md states it at the
   word level (`[QUOTE DESIGN.md:1575, §35]` "Its word is the word of `x`"; `[QUOTE DESIGN.md:1701-1702,
   §36]` "address equality does not change when contents do"). Lean encoded slot facts statically over a
   one-value type, where slot equations hold vacuously, and the session then judged that the location
   reading would change the proofs rather than add a case (findings 2 and 3). How to check: try to state
   `cell-same` or §36's read-back in the Lean core.

2. **On a machine-first spec, the slot lemma stops being an obligation of the agreement theorem.** On the
   pure-first route it blocks any machine that skips `at`, and the session records it as owed:
   `[QUOTE lean/HANDOFF.md:89-90]` "The owner confirmed in chat that this lemma is part of the task." If
   the spec's run itself fetches an `at` entry's word from its target, as §36 describes
   (`[QUOTE DESIGN.md:1660-1662, §36]` "A `let` binds it like any return, and the elaborator supplies its
   word from a non-erased entry in the same slot"), then a compiler that does the same agrees with the spec
   whether or not the slot facts hold of the words; that they hold becomes a safety theorem about the spec,
   separate from the compiler's correctness. The same goes for uniqueness: with a mutating spec run, sole
   reference is something one may prove of the spec, not a premise of agreement. The handoff records a
   related exchange, as a session's claim: `[QUOTE scratchpad/handoff.md:28]` "the owner asked, and the
   session answered yes to both, whether the project would not itself prove that the spec makes `unique`
   mean sole reference". Rests on: section 3.7 items 1, 5, and 6, and the size data of section 5. Caveat:
   the agreement theorem then has to say what happens on spec runs that get stuck (for example, be
   conditional on the spec's run not being stuck).

3. **Keep one run.** Lean has three semantic runs and one executable, with `Real` between two of them and
   `MDec`, `Foot`, `Spine`, and `WO` between three `[READ Strip.lean:134-152; Machine.lean:133-196]`; the
   machine proofs are 39% of the lines `[RAN, section 5]`; the oracle was weakened to keep the runs in step
   (3.7 item 9); and pure soundness imports machine notions (3.7 item 8). The full run exists to prove
   SOUNDNESS.md's (S) and (E) and `no_false`, and the handoff says `[QUOTE scratchpad/handoff.md:19]` "No
   `no_false` theorem is expected".

4. **Make the post-erasure code a datatype of the spec, and run that.** DESIGN.md judges several static
   rules on it: `[QUOTE DESIGN.md:821-824, §19]` "Tail position is judged on the post-erasure code, where
   erased positions, types, coercions and placings are gone and every `let` that only renames has been
   resolved away (§33, §42)."; `[QUOTE DESIGN.md:1647-1648, §36]` "The runtime signature of a function
   consists of its non-erased entries that have no written `at`."; `[QUOTE DESIGN.md:1836-1838, §39]`
   "after erasure, with `at` entries omitted, the post-erasure code holds no call that is not skipped, no
   constructor application, no allocation, no store and no copy." And it says the evaluator runs it:
   `[QUOTE DESIGN.md:1180-1182, §27]` "it is elaborated, its erased positions are stripped, the evaluator
   runs the code". Lean has no such object; TAIL.md proposes one after the fact (7(a) item 10). One open
   point TAIL.md raises would need the owner: `[QUOTE lean/TAIL.md:67-70]` "Which lets are folded away:
   section 19's rule only, or also the reference's further folding of lets that bind constants nothing
   mentions (its ASSUMPTIONS 164 and 189). Any difference would show as a tail verdict that differs from
   the reference's."

5. **Carry the mode of each cell operation in the code the spec's elaboration produces, not in side marks.**
   In Lean, in-place update hangs on `Mark`s that an untrusted reader inserts and a second pass vets
   (section 3.4). §37 makes the behaviour a function of the position's multiplicity
   (`[QUOTE DESIGN.md:1768-1773, §37]` "The cell is taken at the multiplicity of the invocation's own
   position (§14), whatever expression `u` is. At `unique` the invocation consumes `u` and creates its
   value at `u`; `(share (u a1 ... an))` is how a `many` value is built in place. At `many` it uses `u` at
   many and produces its value at `many`: at the cell when every store is skipped (below), and otherwise as
   a fresh copy at nothing.").

6. **Use a small-step machine with an explicit stack if `tail`, `notail`, `delegate`, or the driver loop are
   to appear in any theorem.** Rests on 7(a) item 8. It is also the shape a fuel-free evaluator needs: a
   total step function looped by the `Program` driver, of which §42 says `[QUOTE DESIGN.md:1993-1994, §42]`
   "It never recurses, so an unbounded interaction is the driver's loop over total functions." The handoff
   records the owner's version: `[QUOTE scratchpad/handoff.md:20]` "A fuel-free self-interpreter is possible
   because the top level is not a function; it is the continuation that the driver loops over, the
   prelude's `Program` with `Continue` and `Exit` (DESIGN.md §27 and §42)."

7. **Where Lean used fuel, Sleight has three fuel-free shapes.** (i) The spec's judgments as relations: no
   fuel by nature (`RunS`, `RunM` have none). (ii) An evaluator structurally recursive on an erased
   derivation, where one is available (`[RAN]` `halts.sl`, section 2.7). (iii) A total step function under
   the driver. Lean's own mechanism, well-founded recursion on a program-dependent order with a dynamic
   check, is not one of them (section 2.7). Also: the spec's typing rule for a run-position form can take a
   derivation of the run relation as a premise, instead of Lean's fuelled function inside `CoreTy`
   (section 2.6); then no number appears in the spec.

8. **One algorithmic typing judgment that includes uses.** Lean's split (relational `CoreTy`, Boolean
   `usesCore` recomputing types with the checker's functions) is what made `machine_main` a theorem about
   `checkCore = .ok` (3.7 item 7). MINIMAL.md records a matching decision in a session's wording:
   `[QUOTE MINIMAL.md:86-87]` "The relations follow an algorithm, the simplest one that can be written
   down, however slow".

9. **If rejection is to be a theorem, it needs its own relation.** Lean's checker is a total function into
   `Except String {R // Checked P R}` `[READ Check.lean:7, 929]`, so every core program is accepted or
   refused trivially, but a refusal proves nothing, and nothing says that a program is never both.
   MINIMAL.md records: `[QUOTE MINIMAL.md:94-95]` "A positive `Fails` relation records why a program is
   refused, beside the relation that types it." So two handoff items have no precedent in lean/:
   `[QUOTE scratchpad/handoff.md:21]` "It should be a theorem that every program's source code is either
   accepted or rejected as an error." (lean/ starts at `Core`, not source code) and
   `[QUOTE scratchpad/handoff.md:41]` "Whether "never both accepted and rejected" is in scope."

10. **Put elaboration from source text inside the spec, with the evaluation order in it.** Lean's theorems
    start after the reader; 17% of the code `[RAN, section 5]`, every surface rule (slots' minting,
    at-function checks, marks, literal interning, macro expansion: `[READ lean/README.md:327-331, 418-432,
    543-548, 582-586, 606-608]`), and the evaluation order (section 4) sit outside them. The handoff's open
    question `[QUOTE scratchpad/handoff.md:42]` "Where the spec starts: at source text, which item 3 above
    seems to require, or at a core language." has this as its cost on the core-language side.

11. **State agreement as refinement, not equality of outcomes.** DESIGN.md makes the run nondeterministic
    at one form (`[QUOTE DESIGN.md:3044-3046, §67]` "`ENone` proves nothing, so an implementation may always
    answer it, and which one a call answers may differ between runs.") and lets a real run crash
    (`[QUOTE DESIGN.md:1320-1321, §31]` "A real run may crash where the host cannot represent what is asked
    of it. A crash produces no value, never a different one."). Lean's proofs lean on determinism of the
    stripped run (`RunS.det` is used at MachineAsm.lean:1653, MachineDeleg.lean:371, MachineRun.lean:527,
    1616, 1777, and Sound.lean:3198, 3641, 3684, `[RAN] grep -n "RunS.det\|\.det h" lean/Minimal/*.lean`),
    which is available only because `slot-eq` and crashes are outside its fragment.

12. **Choose the address model knowingly.** Lean's bump counter makes runs deterministic and makes
    freshness a numeric comparison (`H.next ≤ b` in `MOut`, `[READ Machine.lean:11-12;
    MachineSound.lean:953-961]`), at the price of an order on addresses. DESIGN.md is silent on any such
    order: `[RAN] grep -n -i address DESIGN.md` printed one line, 1701 ("address equality does not change
    when"), and `grep -n -i pointer DESIGN.md` printed six, none about order or arithmetic. The handoff's
    proposal B is the abstract alternative, `[QUOTE scratchpad/handoff.md:36]` "an address is an abstract
    name for a block, with no order and no arithmetic; a step that allocates may take any address never
    taken before"; it removes the order but makes every statement hold only up to a renaming of addresses.
    Neither is free.

13. **Thread the store through elaboration.** Lean's checker keeps known values as immutable stripped
    trees (`Ctx.fixed : List (Option Tm)`, `[READ Typing.lean:58, 132-135]`), which suits a pure run. With a
    mutating run, a `Settled` value lives in a heap that later top-level forms can mutate; DESIGN.md already
    speaks this way (`[QUOTE DESIGN.md:1355-1356, §32]` "A top-level binder, which is a `Settled` (§29), may
    be `unique` under the same rules, since run-position statements are sequential.";
    `[QUOTE DESIGN.md:2882-2885, §65]` "The macro world is the elaborator's program store:
    the run-position entries with their values and facts, the literal table, the gensym counter and the
    expansion count. It is threaded sequentially through all of elaboration"; `[QUOTE DESIGN.md:2848-2850,
    §64]` "none for an `MUnique` handle, whose read would happen outside the elaborator's use accounting,
    possibly after the value was consumed and mutated in place.").

14. **Separate words from terms.** Lean's single `Tm` (section 3.1) goes with a machine that does not
    express §33's representation (section 3.3). MINIMAL.md records the opposite choice for mini/:
    `[QUOTE MINIMAL.md:96-97]` "`Term`, the type of types and `is` expressions, and `Val`, the type of
    runtime values, are separate ADTs." How much of §33 the spec states is for the owner; §33 introduces it
    with `[QUOTE DESIGN.md:1459-1460, §33]` "Coercion is free only if the representations coincide, so the
    following is a requirement on the implementation."

15. **Decide early whether the spec runs extern models or implementations.** The handoff lists it as open:
    `[QUOTE scratchpad/handoff.md:36]` "Not worked out: which kind of word a function value is, and whether
    the spec runs the prelude's models of extern types and functions or the FFI implementations." Lean ran
    models and paid for it twice: the full run cannot compute the prelude (3.7 item 10), and making six
    arithmetic functions native took most of a 2,013-line file (section 5).

16. **Induct on derivations, not on the evaluator.** Both of Lean's large theorems are functional
    inductions over `eval` (2.4, 2.5). A Sleight evaluator cannot be that function (2.7), so the Sleight
    proofs would recurse on derivation values of the run relation, which are finite trees and can be
    `subterm` arguments (`[RAN]` `halts.sl`; mini/ already writes judgments this way,
    `[QUOTE mini/README.md:3-7]` "each judgment is an ADT whose constructors are its rules, and beside each
    relation stands a function that derives it by structural recursion, or answers "stuck" on a shape the
    rules have no derivation for (evaluation alone still burns fuel)").

---

## 8. Contradictions with DESIGN.md, and session assumptions presented as fact

DESIGN.md wins in each case.

1. **The full semantics of SOUNDNESS.md is not the run DESIGN.md describes.** SOUNDNESS.md's full semantics
   runs erased code on immutable trees with a run-time level counter `[READ SOUNDNESS.md:113-121, quoted in
   section 6]`. DESIGN.md: `[QUOTE DESIGN.md:1319-1320, §31]` "Evaluation is eager. The semantics is that of
   a machine with unlimited stack and heap."; `[QUOTE DESIGN.md:1279-1280, §29]` "its value was never
   computed, because the erased positions are stripped before the evaluator runs"; `[QUOTE
   DESIGN.md:1247-1248, §29]` "a function's value is its compiled code, a `Level` is an erased token".
   SOUNDNESS.md hedges its reading, `[QUOTE SOUNDNESS.md:118-119]` "That reading is OPEN.md 2's first step
   and OPEN.md 3.", so this is a proof device, not a false claim; the risk is a later session taking it for
   the language's run. The same holds for lean/'s `eval` `[INFERENCE]`.

2. **`Slot` has a constructor in lean/.** `[QUOTE lean/README.md:537-539]` "`Slot` is a built-in type with
   one constructor and no `Matchable`, and `vacant-slot` is that constructor" against `[QUOTE
   DESIGN.md:1800-1801, §38]` "`Slot` is an opaque nullary type with no constructors and no `Matchable`
   (§8)." The README describes its model openly, but the difference is not in the list it offers the owner
   under `[QUOTE lean/README.md:647]` "## Shapes chosen here, for the owner to confirm or change":
   `[RAN] awk 'NR>=647 && NR<=780 && /Slot|slot/' lean/README.md` printed nothing. It is the choice that
   makes slot facts vacuous (finding 2).

3. **The README says the machine writes a `cell-write` in place; the code does not store.** `[QUOTE
   lean/README.md:181-182]` "a cell invocation or `cell-write` at `unique` written into its block in place"
   and `[QUOTE lean/README.md:610-611]` "the machine run writes a cell invocation or `cell-write` at
   `unique` into its block in place". `[READ Machine.lean:73-95]`: only `Prog.reuse` (the invocation) calls
   `H.write`; `.write true` yields the pointer. The handoff file describes the code more exactly:
   `[QUOTE lean/HANDOFF.md:74-76]` "cell invocations at unique written in place (`Prog.reuse`),
   `cell-alloc` allocating".

4. **The README's ownership sentence is stronger than the top-level theorem.** `[QUOTE
   lean/README.md:183-185]` "Its results stand for the stripped run's, and the blocks a `unique` result
   owns are reached by nothing else live (`MOut`; `Spine` and `WO` are the ownership relations)." At
   `machine_main` the list of unique results is `[]`, so that part of `MOut` is vacuous there (section
   2.5, `[INFERENCE]` from the definitions). §27 has the driver consume a `Program` at `unique`
   (`[QUOTE DESIGN.md:1165-1167, §27]` "A `Program` value (§42) is run: the driver consumes it at `unique`
   and applies each step's continuation once."); no Lean theorem covers that.

5. **Two citations of §42 for functions §42 does not name.** `[QUOTE lean/HANDOFF.md:17-18]` "`nat-same`
   and the other functions DESIGN.md section 42 builds on it" and `[QUOTE SOUNDNESS.md:206-207]` "a
   `*-same` function of §42". `[RAN] grep -n -e "-same" DESIGN.md` finds only `cell-same` and `fn-same`
   (lines 615, 616, 2453, 3048, 3057, 3117, 3119, 3125). The functions are in `lib/prelude.sl`
   (`[RAN] grep -n "nat-same" lib/prelude.sl`, first hit line 2267), of which §42 says
   `[QUOTE DESIGN.md:1966, §42]` "`lib/prelude.sl` is the reference for what it defines."

6. **A README attribution to §65 that §65 does not make.** `[QUOTE lean/README.md:649-650]` "`MacroWorld`
   and `Gensym`, which DESIGN.md section 65 declares opaque". §65's words are `[QUOTE DESIGN.md:2887-2888,
   §65]` "It has no constructor and is no entry, so a non-erased one never escapes an expansion"; the
   declaration as opaque is `lib/prelude.sl`'s (`[RAN] grep -n def-opaque lib/prelude.sl` printed, among
   four lines, `1996:(def-opaque $ (MacroWorld : -> Type))`).

7. **Owner statements that exist only as a session's report of a chat.** Not contradictions, but they
   should not be cited as decisions: `[QUOTE lean/HANDOFF.md:61]` "On the plan agreed in chat:";
   `[QUOTE lean/HANDOFF.md:89-90]` "The owner confirmed in chat that this lemma is part of the task.";
   `[QUOTE lean/HANDOFF.md:193-194]` "`coerce` rests on how the compilers make coercion sound, an account
   a session read and the owner agreed with in chat."; `[QUOTE OPEN.md:11-12]` "The owner holds that it is
   sound."; `[QUOTE OPEN.md:37]` "The owner believes it is sound."; `[QUOTE README.md:113-114]` "The author
   asserts that each Sleight function terminates by a lexicographic order". The machine plan of
   `[READ lean/HANDOFF.md:58-72]` also predates the owner's present view as the current handoff reports it
   `[READ scratchpad/handoff.md:23-24]`.

8. **MINIMAL.md's recorded decisions and lean/ go opposite ways on three points, unlisted.** MINIMAL.md
   attributes its cuts to the owner and its wording to a session (`[QUOTE MINIMAL.md:5-7]` "The cuts are
   the owner's decisions of one design session; the wording, and every claim about what a cut takes with
   it, is that session's reading and may be mistaken."). It records `[QUOTE MINIMAL.md:84]` "Evaluation and
   typing are relations, not functions.", a `Fails` relation `[READ MINIMAL.md:94-95]`, and separate `Term`
   and `Val` `[READ MINIMAL.md:96-97]`. In lean/, the primary evaluator is a function, there is no `Fails`,
   and `Tm` is one sort (sections 2.1, 2.6, 3.1). The README's section `[QUOTE lean/README.md:265]`
   "## Differences from MINIMAL.md" lists one item, about `def-adts` signatures
   `[READ lean/README.md:265-273]`. DESIGN.md is silent on how a formalization should be shaped, so this is
   two session documents disagreeing, not a breach of DESIGN.md.

9. **The measure's missing places.** SOUNDNESS.md pads a measure with a top element (`[QUOTE
   SOUNDNESS.md:243-245]` "the positions from n+1 to k hold ⊤, a value above every tree"); the Lean check
   reads a missing place as 0 (`a.headD 0`, `[READ Eval.lean:7-9]`). I believe this is harmless, because
   §19 requires the enclosing function to have a `subterm` parameter at the decreasing index
   (`[QUOTE DESIGN.md:809-810, §19]` "The enclosing function must have a subterm parameter at that
   index."), but the two descriptions are not the same order `[INFERENCE]`.

10. **The oracle is coarser than `world-do`.** `[QUOTE lean/README.md:658-659]` "The oracle that answers a
    `world-do` is keyed by the world's step number and the request's constructor alone, not the request's
    fields". So the hypothesis `OracleOK` cannot express an answer that depends on a request's fields
    `[INFERENCE from Sound.lean:1522-1528]`. The README lists this itself among the shapes for the owner
    `[READ lean/README.md:647-663]`.

---

## Things I am least sure of

1. **Whether the Lean development builds.** Not checkable here. All "proved" claims are statements I read
   plus the READMEs' word.
2. **My reading that `cell-write` stores nothing and that fieldless constructors are heap blocks.** Both
   rest on reading `Machine.lean:19-95` and `Reader.lean:2055-2073, 2376-2386`, not on running the model.
   I did not read the 16 places in `MachineRun.lean` that mention `H.write` in proofs.
3. **The vacuity of the ownership clauses at `machine_main`.** It follows from `ru = []` in the statement
   and the definitions of `MOut`, as I read them; I did not trace the proof.
4. **The claim that Lean's fuel-free `eval` cannot be transcribed into Sleight.** It rests on a
   session-written README sentence reporting the owner's assertion about the language's strength, and on a
   standard diagonal argument I did not formalise. The positive experiment (`halts.sl`) shows only that
   recursion on an erased derivation works for a toy machine.
5. **Attributing pain to modelling choices.** The lean/ documents are written in the present tense and
   never say a choice was wrong (section 3.7's grep). I inferred cost from "Not done" lists, deferrals,
   the "not a case beside the existing ones" sentence, and file sizes. The owner's view reaches me only
   through the handoff.
6. **Inference 7(b)2** (that on a machine-first spec the slot lemma and sole-reference property leave the
   critical path). It is an argument about a design that does not exist yet; it depends on how the
   agreement theorem treats stuck spec runs.
7. **Whether `RunM` is deterministic**, and whether `lean/prelude.sl` and the test counts in HANDOFF.md
   are current.
8. **Coverage of the Lean sources.** I read `Sound.lean`, `Check.lean`, `Native.lean`, `Reader.lean`,
   `MachineSound.lean`, `MachineRun.lean`, and `MachineAsm.lean` only around the statements cited; a
   definition I did not open could qualify something above.
