# Draft: the staging model — DESIGN.md/KERNEL.md/kernel_input.ml edits

Staged for owner review; nothing applied. This supersedes the committed
§18 (two global silos, double-writes), parts of §3 and §34 (block
boundary rules, flagged item 4), and the comptime-expression surface.
Wording aims to be commit-ready; hedging per CLAUDE.md rule 1; no
breadcrumbs in applied text.

## Context for a fresh session (prose only — not proposed doc text)

This draft is the endpoint of a long design session (2026-08-16/17).
The committed DESIGN.md contains an *intermediate* model that this
draft replaces — do not treat committed §18/§34 as settled; they were
committed mid-session and the owner then iterated further in chat.
Key history and rationale, so the proposed edits read as conclusions
rather than assertions:

1. **Why comptime became a statement qualifier.** Comptime blocks were
   doing two unrelated jobs: evaluate-early and level-hoisting (§36
   split off the latter as v2 `hoist`). Per-statement staging
   (REPL-style: each qualified statement fully checks, runs, stores
   before the next) makes a multi-statement block equivalent to
   consecutive qualified statements, so the block form is redundant.
   Owner prefers the spliced-head spelling, no extra parens.

2. **The history of "when are definitions Const".** A blanket
   "definitions birth Const" died to closures (a nested definition
   capturing a runtime local has no value at elaboration). A
   capture-conditional rule ("Const iff captures Const") was rejected
   by the owner as fragile/spooky-action-at-a-distance. A qualifier
   with a Const-captures *check* was the next stop. The final model
   subsumes all of it structurally: the enter-copy (below) means a
   staged definition *cannot* reference enclosing runtime locals, so
   no side condition is needed at all.

3. **The staging discipline is the owner's mental model, verbatim in
   spirit**: enter = copy const silo to working dyn silo; work =
   elaborate through the one ordinary code path ("forget we're
   comptime"); leave = working silo returns as the new const silo,
   appended entries re-projected into the outer dyn silo
   (re-canonicalized there, level-birth flag stripped). One
   elaboration routine; comptime is a wrapper.

4. **Why a staged `def-fns` group is Dyn inside its own bodies**
   (owner-found hole): were the group Const during its own
   elaboration, a nested staged statement inside a body could call
   the group at elaboration time — unbounded elaboration-time
   recursion. Under the model this is unrepresentable: the nested
   enter copies a const silo that does not yet contain the group.

5. **Why tombstones**: with silos as pure presence/absence, a staged
   statement resolving a name shadowed by a runtime binding would
   fall through to a stale older Const entry. A Dyn binding therefore
   writes an Inacc tombstone into the const silo; the enter-copy
   carries it, so the nested statement errors loudly.

6. **The `prove-predates` rules and the two-route attack** (why both
   the membership condition and the flag condition are necessary): a
   runtime binding lexically precedes a staged level but temporally
   postdates it; if the false `Predates` fact can be born either
   inside the staged context (route 1: tombstoned argument) or
   outside it (route 2: escaped level keeping its flag), an
   `M`-leveled function reachable from `I`-leveled code with `M > I`
   yields a proof-carrying call cycle with no decrease. Flag placement
   (born into the executing regime's silo; copied down at enter;
   stripped at re-projection) closes route 2; tombstone membership
   closes route 1.

7. **Why per-fact validity tags lost to whole-silo separation**
   (owner's argument): rules are recorded *after* canonicalizing
   against the rules in force, so a fact born under hypotheses has
   them baked into its normal form; no tag undoes that. Hence
   re-projection re-canonicalizes, and the same fact may take
   different normal forms per silo, correctly.

8. **Why plain nested `def-fns` must NOT copy** (only staged entry
   copies): the factory pattern requires nested bodies to capture
   enclosing runtime locals (§33's `map` captures `pml`); hard-mode
   exercises showed the factory is the *only* pattern by which
   runtime-manufactured functions get called, so breaking it is not
   an option.

9. **"A body calls only into the past; execution births only
   futures"** — the observation (from a worked exercise, recorded
   hedged in the new §33 bullets) explaining why variant 2 hoists
   manufacture above `(def-lvl G)`: a level born during a body's
   execution postdates the body's own level, so no `Predates` proof
   into it can exist.

Also settled earlier in the session and already committed (kept by
this draft): Const/Dyn/Inacc naming; the optional type/multiplicity
assertion 2×2 on `let`/`match`/`values` with hard errors both ways;
comptime-match's mismatch printing as a diagnostics channel; argument-
less `inacc`; the interpreter-trust note in KERNEL.md (`Maybe`/forged
erased `False` field; kernel reference evaluator as v2 obligation,
load-bearing for §10); §35 macro-hygiene sketch and §36 `hoist` v2
sketch. Working agreement reminders for the fresh session: CLAUDE.md
rule 11 (decisions are proposed in chat first, never invented into
committed files, however flagged); rule 1 hedging; the owner keeps the
main documents lean — context/justification belongs in chat or in
clearly-separated prose like this section, not sprinkled through
DESIGN.md; KERNEL.md records implementation decisions only. The
worked examples below were paren-balance-checked by script;
`lib/kernel_input.ml` compiles as committed, with §I's deltas to
apply on approval.

Items in this draft that were never explicitly ruled on, called out so
approval of the draft is informed:

- (i) Plain top-level calls are proof-free (top level sits above every
  ordinary level, staged or not) — needed for the comptime-free
  example's bare `(map-factory I)`.
- (ii) §31's `List` and §32's `Nat` definitions gain the `comptime`
  qualifier (their constructors are referenced from staged statements
  in §33's first usage variant).
- (iii) The "calls reach only the past" observation is recorded as a
  hedged bullet in the new §33 example, not as normative §7/§8 text.

## A. Surface: `comptime` is a statement qualifier

- The `comptime` expression form is retired. `comptime` qualifies
  exactly one statement, written with the statement's head spliced —
  `(comptime def-fns I ...)`, `(comptime let ML map-nat ...)` — no
  extra parentheses. Multi-statement staging is consecutive qualified
  statements; each is its own unit, elaborated and executed in order
  (REPL-style), so a later staged statement sees the births of earlier
  ones.
- §16: delete "A file's top level counts as being inside a comptime
  block (§24), so calls there need no proofs. Worth revisiting." and
  the comptime-boundary sentence added after it. Replace with:

  > A file's top level is the program: its unqualified statements are
  > the runtime program, its `comptime`-qualified statements are the
  > compile-time part. Calls at top level need no decrease
  > annotations, qualified or not — the top level sits above every
  > ordinary level (§24).

- §16's statement list: `comptime` joins as a qualifier applicable to
  any of the five statements, not a sixth statement.
- §24 rewritten (title: "Staged elaboration calls freely"):

  > Within a `comptime`-qualified statement's elaboration — directly
  > in it, not inside a function body defined there — any type or
  > value constructor can be invoked, and so can any function, with no
  > `Predates` or `Subterm` proof at all. The same holds at a file's
  > top level (§16). In a sense this context sits at the "highest"
  > level, above every ordinary function level.
  >
  > The owner's reasoning for why this should still be sound: there is
  > no way for an ordinary (leveled) function's body to call *into*
  > staged elaboration, so this unrestricted-calling privilege can
  > never be reached through the leveled function-call graph that §7's
  > termination machinery actually checks. Recorded as the owner's
  > claim, not a verified result.

- §27 item 15 becomes:

  > 15. `comptime` — statement qualifier: the qualified statement
  >     elaborates and executes at compile time under §18's staging
  >     discipline; its births are promoted to `Const` on completion.
  >     Written with the statement's head spliced:
  >     `(comptime def-fns ...)`.

- §4's "`Dyn` while evaluating inside a comptime block" → "`Dyn`
  during a staged statement's elaboration".

## B. §3 — registry and silo pointer

Replace the committed silo paragraph ("An entry's **type** and its
**"is" statement** ... write both (§18).") with:

> An entry's **type**, its **"is" statement** (a
> rewrite/canonicalization rule), and its **level-birth flag** (§8)
> live not on the entry but in the two silos (§18): two payload
> columns over this one shared spine, so shadowing resolves once, for
> both regimes. Each payload is either real data or an `Inacc`
> tombstone; which column carries what is governed entirely by §18's
> write rules. A type or `is` is just a tree whose leaves are
> references to entries in this same table (§5); an `is` tree may
> reference its own entry.

- The registry bullet list loses the standalone **level-birth marker**
  bullet (the flag is silo payload now); `prove-predates`'s
  requirement moves to §18. The `Inacc` paragraph becomes: "`Inacc` is
  not a stored state but a tombstone payload (§18); an entry is
  inaccessible to code whose silo holds its tombstone, and the silos
  may not be queried about it from there — any lookup is an access
  error."
- The state bullet becomes derived: "a **state** — derived, not
  stored: `Const` means real payload in the const silo (with a stored
  value in this registry), `Dyn` means real payload in the dyn silo
  only, `Inacc` means tombstoned in the silo doing the asking."

## C. §18 — full replacement

> ## 18. The two silos, staging, and match-branch rewriting
>
> The scope spine (§3) carries two payload columns, the **silos**:
> **const** and **dyn**. A payload is either real data — the entry's
> type, its `is` rule, and its level-birth flag (§8) — or an `Inacc`
> **tombstone**. Names resolve once against the shared spine; the
> payload is then read from the silo of the code doing the asking:
> ordinary elaboration reads dyn; macro/special dispatch (§4) and the
> other Const-inspection sites (§34) read const. Hitting a tombstone
> is an access error.
>
> **Write rules.**
>
> - An ordinary binding writes real payload to dyn and a tombstone to
>   const. The tombstone is load-bearing for shadowing: staged code
>   resolving a name shadowed by a runtime binding must error loudly,
>   not fall through to a stale older `Const` entry.
> - The `inacc` form (§27) tombstones both silos.
> - A `comptime`-qualified statement writes through the staging
>   discipline below.
>
> **The staging discipline.** Elaborating a qualified statement is a
> re-entrant call:
>
> 1. **Enter.** The working dyn silo becomes a copy of the current
>    const silo — level-birth flags and tombstones included. Every
>    runtime binding of every enclosing body is thereby out of reach
>    (its tombstone came along); everything previously promoted is in
>    reach.
> 2. **Work.** Elaboration proceeds through the one ordinary code
>    path, exactly as unstaged code would: bindings, function bodies,
>    `def-lvl` flags, branch layers, all writing the working dyn silo.
>    Calls here are proof-free (§24), and a `let`'s right-hand side
>    that computes is run by the interpreter (KERNEL.md) with the
>    results stored. Notably, a staged `def-fns` group is **`Dyn`
>    during its own elaboration** — the group's entries are ordinary
>    working-silo entries, promoted only at leave. Consequence: a
>    nested qualified statement inside one of the group's bodies
>    copies a const silo that does not yet contain the group, so
>    elaboration-time self-recursion is not forbidden but
>    unrepresentable. A staged definition exists only in its own
>    future.
> 3. **Leave.** The working dyn silo is returned upward as the new
>    const silo. Each entry it appended is then **re-projected** into
>    the outer dyn silo: its type and `is` are canonicalized against
>    that outer dyn silo before being recorded there, and its
>    level-birth flag is **not** copied. Stored values (§3) were
>    recorded in the registry as the statement ran; the re-projected
>    entries are what the surrounding code sees, `Const` by §34.
>
> The delta a leave promotes is strictly appended entries plus one
> exception: `comptime-match` (§15) may have recorded a verified fact
> about a pre-existing `Const` entry, and that fact promotes too — it
> was checked against a real stored value. Branch layers never
> promote; they pop before leave.
>
> Because re-projection re-canonicalizes, the same fact — a type
> included — may take different normal forms in the two silos, and
> that is correct: each silo is self-consistent under its own
> canonicalization, and a fact is only ever read in the silo whose
> rewrites shaped it. This is also why the split is by whole silos
> rather than validity tags on individual facts: fact *creation*
> depends on the facts already in force, so a tag cannot undo the
> context a fact was canonicalized in.
>
> **`prove-predates` is a silo query.** Both arguments must resolve to
> real payload in the silo the proving code reads, and the `Level`
> argument must carry the level-birth flag there. The flag's placement
> does the safety work: a runtime `def-lvl` flags the dyn silo it was
> born in; a staged `def-lvl` flags the const silo at its leave; enter
> copies flags downward into fresh staged contexts; re-projection
> strips them. We believe both halves are necessary: dropping either
> admits a `Predates` fact whose introduction order disagrees with
> real birth time (a runtime binding lexically before, but temporally
> after, a staged level), from which an `M`-leveled function reachable
> from `I`-leveled code with `M > I` gives a proof-carrying call cycle
> with no decrease — argued as an attack sketch, not verified.
>
> **Match-branch rewriting** (mechanics unchanged):
>
> - Before an occurs-check, and before recursing into any equation's
>   LHS or RHS, both sides are first canonicalized/rewritten to normal
>   form via the applicable `is` facts, in the silo at hand.
> - The canonicalization engine deliberately does not consult a `Const`
>   entry's actual stored value — it works uniformly, driven solely by
>   `is` facts, even though `Const` carries strictly more information.
>   A deliberate simplification, not an oversight.
> - Entering a branch **forces** a unification: the scrutinee is
>   equated with the branch's constructor applied to the newly-bound
>   fields, and the scrutinee's type is equated with the type computed
>   from that same constructor application, recorded as a branch layer
>   on the current dyn silo and popped at branch exit — §16's "none of
>   it survives the match," made mechanical. "Forces" means this isn't
>   a passive check — it's licensed to add new `is` facts outright
>   (recursively, into matching non-atom arguments) wherever doing so
>   isn't already provably impossible.
> - This is sound because a branch's unification only ever happens as
>   the consequence of a branch that was actually, genuinely entered —
>   gated by a real discriminant check (a runtime tag comparison for a
>   non-erased enum, or `comptime-match`'s compile-time computation) —
>   not performed as a free-floating comparison between two arbitrary
>   atoms.
> - The only two ways forcing a unification fails, i.e. produces a
>   contradiction: (1) `x` equated with an expression containing `x`
>   (checked after resolving through any existing atom-to-atom
>   `is`-alias chains, not just against a new equation's literal
>   surface form; `x = x` itself is a no-op, not a contradiction);
>   (2) two already-known, distinct constructors equated (arity
>   mismatch is one easy sufficient symptom of this given fixed
>   arities and no currying, not a separate case).

## D. §34 — full replacement

> ## 34. Const formation and compile-time inspection
>
> The states are `Const`, `Dyn`, and `Inacc` — derived from the silos,
> not stored (§3, §18). This section collects how `Const` arises and
> what may be done with it.
>
> **Const values are born with known erasure.** The births:
>
> 1. **Promotion at a staged statement's leave** (§18) — the
>    statement's appended entries, with erasures declared by the
>    producing forms: a call's callee return telescope, a
>    constructor's declaration (§34 head rule below), `def-fns`
>    entries `many`, a `Level` or `Matchable` an erased token, plus
>    the optional `let`/`values`/`match` assertions (§9, §11) where
>    the producer alone is ambiguous. This is what licenses running
>    the statement before its surroundings are finished: nothing about
>    its erasure depends on code after it (§20).
> 2. **`comptime-match` field binding** (§15) — erasure is the field's
>    declared multiplicity.
> 3. **State-inheriting `let`** (§9) — strictly propagation.
>
> Nothing else births `Const`. In particular a constructor application
> over `Const` arguments is still `Dyn` (§15) — stage the binding if
> `Const` is wanted. A staged `def-fns` group is not `Const` inside
> its own bodies (§18) — promotion strictly postdates the statement.
> Prelude entries — `Special`'s variants, `Univ`/`Type`, the §8
> axioms, and any prelude functions — are `Const` by fiat of the
> implementation; no user statement births them.
>
> **Inspection requires Const and non-erased.** A `Const` entry's
> stored value is read in three places: §4's head dispatch (invoking a
> `Special` or `Macro`), `comptime-match`'s discriminant read (§15),
> and the execution of a staged statement that references the entry —
> the value gets embedded into the code the interpreter runs. §18's
> rewrite engine consults no stored values. All three require the
> entry to be `Const` and non-erased: an erased `Const` entry stores
> only §3's existence token, the value behind it never having been
> computed — erased positions are stripped before the interpreter runs
> (KERNEL.md). For staged execution this requirement is just erasure
> checking doing its job: an erased `Const` may still be referenced
> from erased positions, which are stripped, not read.
>
> **The checker never evaluates.** The dividing line for what the
> checker itself computes: only work whose entire trace is spelled out
> in the source. Constructor application assembles data whose shape
> the source dictates; `comptime-match` *verifies* an asserted
> discriminant and projects — the programmer wrote the answer down.
> Selecting a match branch from a value would be the value steering
> elaboration — the first step of evaluation — so `match` results stay
> `Dyn` (§15) even on a `Const` scrutinee; the delimited alternative
> is staging the binding, handing the branching to the interpreter.
> By the time any inspection site runs, the inspected entry's erasure
> is already settled, so no erasure demand ever flows backwards into
> code that has been checked, stripped, and run — the same shape as
> §18's rule that nothing hypothetical crosses a staging boundary.
>
> §23's invariant appears to survive all of this: stripping erasure
> only turns erased positions non-erased, so a program valid under
> these rules should remain valid — argued by inspection, not
> verified.

(The committed §34's boundary tail-form list, nullary-function
analogy, and flagged item 4 are all deleted by this replacement.)

## E. §15 touch-ups

- "a value crossing out of a comptime block becomes `Const` (§24)" →
  "a staged statement's births are promoted to `Const` at its leave
  (§18)". "An `Inacc` value crossing out is a compile error" — folded
  into §18's tombstone rules; delete the sentence.
- The ctor-app paragraph's "so a definition wanted as `Const` is
  wrapped in `comptime` (see §33's `xs`)" → "so a binding wanted as
  `Const` is staged: `(comptime let xs ...)` (§33)."
- comptime-match text otherwise stands as committed.

## F. §31–§33 example edits

- §31: `(def-adts` → `(comptime def-adts` (one token; List's
  constructors are referenced from staged statements in §33).
- §32: `(def-adts $ Nat ...` → `(comptime def-adts $ Nat ...`;
  `length`'s `def-lvl`/`def-fns` stay plain.
- §33: the factory half gains qualifiers:

  ```scheme
  (comptime def-lvl F)

  (comptime def-fns F $ map-factory : ...unchanged...)
  ```

  The usage half is replaced by two variants.

  **Variant 1 — staged:**

  ```scheme
  (comptime def-lvl I)

  (comptime def-fns I $ inc : (many (Nat) n) -> (many (Nat) m)
    (Succ n))

  (comptime let ML map-nat (map-factory I))

  (comptime let xs (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

  (comptime let out (map-nat (Nat) (Nat) inc xs))
  ```

  Bullets: every call is proof-free (§24); each statement's births
  promote at its leave, so each later statement finds its
  predecessors `Const` (§18); `ML` is erased and `map-nat` `many` by
  `map-factory`'s return telescope, `xs` `many` by the constructor
  head rule (§34); `inc` is `Dyn` inside its own staged statement and
  `Const` only after it (§18).

  **Variant 2 — no staging at all:**

  ```scheme
  (def-lvl I)

  (let ML map-nat (map-factory I))

  (def-lvl G)

  (let pMG (prove-predates ML G))

  (def-fns G $ run : -> (many (List (Nat)) out)
    (def-fns I $ inc : (many (Nat) n) -> (many (Nat) m)
      (Succ n))
    (let xs (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))
    (map-nat (predates pMG) (Nat) (Nat) inc xs))
  ```

  Bullets: manufacture is hoisted above `(def-lvl G)` because
  `map-nat`'s level is born at the factory call, and a level born
  after `G` could never predate it — we believe, from working these
  examples, that a body can call only into the past while execution
  births only futures, staging being what licenses the exceptions
  (recorded as an observation, not a rule); `pMG` shows a returned
  level serving `prove-predates` in first position — only the second
  position needs the level-birth flag (§18); `inc` is passed, never
  called directly from `run`, so no proof relating `I` to `G` is
  needed; nothing here is staged, so no silo but dyn is ever written
  beyond tombstones.

## G. §35/§36 wording

- §36 (`hoist`): "a comptime block is how manufacture runs early" →
  "a staged statement is how manufacture runs early"; "the comptime
  analogy" sentence unchanged otherwise.
- §35: no changes needed.

## H. KERNEL.md

- Round-trip section: "a comptime expression" → "a staged statement's
  computing right-hand sides"; the dialogue-runs-both-ways paragraph:
  "A block's boundary erasures (§34) are settled before it is stripped
  and run" → "A staged statement's escape erasures (§34) are settled
  before its code is stripped and run".
- New short implementation note (KERNEL.md being the implementation
  record):

  > ## Staging implementation
  >
  > There is one elaboration routine; `comptime` is a wrapper around
  > it. The silos are persistent structures, so the staging
  > discipline (§18) is cheap: enter copies a pointer, work threads
  > the pair through the ordinary code path, leave returns the working
  > silo as the new const silo and re-projects the appended entries.
  > The recursion is the host call stack; body exit restores silo
  > values by ordinary scoping, which is what makes staged births
  > lexically scoped for free.

## I. kernel_input.ml deltas (applied on approval)

- `stmt` gains the qualifier: `Staged of stmt` (wrapping any of the
  five; nesting `Staged (Staged _)` rejected by the kernel).
- The `Comptime of mult list * expr` comp is deleted (no expression
  form). `NoProof` remains for staged-context and top-level calls.
- Everything else unchanged; `ComptimeMatch` stays a statement.
