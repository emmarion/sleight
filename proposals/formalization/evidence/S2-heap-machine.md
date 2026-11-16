# S2: a mutating heap machine written as relations in Sleight (spike)

Written by a Claude session for the lead session. Nothing here is the owner's decision. The language modelled
is a small model built for study; **it is not DESIGN.md's stripped language**, and section 10 lists what it leaves out.

**Where the code is.** `S2/` below means
`/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/S2/`.
`/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/S2/RUN.md` lists the commands.
Every command in this report was run in that directory with these shell variables:

```sh
B=/home/user/sleight/_build/default/bin/main.exe
LIB="/home/user/sleight/std/list.sl /home/user/sleight/mini/base.sl"
SPEC="$LIB heap.sl code.sl big.sl small.sl"
FNS="heap-fn.sl prim-fn.sl run-fn.sl step-fn.sl"
```

`S2/run-all.sh` runs all of them; `S2/run-all.log` is its output. Every run prints one `(MkUnit)` first, which is
the final expression of `mini/base.sl`, not of the spike.

**Tags.** `[QUOTE file:line]` exact text (a quote that spans lines has its line breaks replaced by spaces);
`[RAN]` a command I ran and its output; `[READ file:lines]` what I read in code; `[INFERENCE]` reasoned, not
verified; `[UNKNOWN]` not determined.

---

## 0. Findings, most decision-relevant first

1. **A mutating heap machine can be written as relations in Sleight, in both styles, and the checker accepts it.**
   [RAN] `./run-all.sh > run-all.log 2>&1; grep "^exit" run-all.log | sort | uniq -c` printed `14 exit 0` and
   `7 exit 1`; the seven failures are the seven files under `S2/neg/`, written to be refused (section 7).
   [RAN] the same script with `B="/home/user/sleight/_build/release/slc --interpret"` gave the same 21 exit
   codes in the same order, and `diff` found the output of the 14 successful runs identical to the reference's.
2. **Size.** The specification is 160 non-blank lines, the deriving functions 248, and the proof files, with
   one experiment file, 836.
   [RAN] `grep -c . FILE` per file; table in section 3. Checking everything but the examples takes under a
   second: [RAN] `time $B $SPEC $FNS det.sl keep.sl agree.sl ren.sl ren-small.sl ren-grow.sl ren-online.sl abs.sl stated.sl`
   printed `real 0m0.746s`, and `time $B $LIB` alone printed `real 0m0.483s`.
3. **Big-step and small-step share every rule that touches the heap.** One relation, `Prim`, says what one
   instruction does to a heap; S-big adds 4 rules and S-small adds 5 plus the 2 of its closure.
   [READ S2/code.sl:49-65, S2/big.sl:8-25, S2/small.sl:12-35]. Every `Run` derivation gives a `Steps` derivation:
   proved, `big-small` [READ S2/agree.sl:9-37]. The converse is stated and not proved [READ S2/stated.sl:3-7].
4. **Recommendation [INFERENCE]: make the small-step relation the definition, and keep the big-step relation as
   a presentation proved to agree with it.** Reasons, with their evidence, are in section 9.1. The owner has not
   ruled on this.
5. **Nondeterministic addresses in the spec cost three rules** (`Fresh` 2, `Alloc` 1) [READ S2/heap.sl:15-19, 31-33]
   **and one invariant in the deriving function** (`Below`, "every address in use is below the counter", 30 lines
   with its lemmas) [READ S2/heap-fn.sl:22-51]. A counter in the spec itself would not remove that invariant
   [INFERENCE, section 9.2].
6. **All three obligations of the brief are proved, not just stated.** (a) Determinism once the choices are fixed:
   `run-det`, `step-det`, `steps-det` [READ S2/det.sl:111-182]. (b) Invariance under renaming of addresses, in two
   forms: for a whole run given the renamed choices (`ren-run`, `ren-steps`) and one step at a time for any fresh
   address the second machine picks (`sim-alloc`, `sim-quiet`) [READ S2/ren.sl:227-251, S2/ren-small.sl:53-65,
   S2/ren-online.sl:40-67]. (c) A block keeps its address, tag, and size, and no address is taken twice:
   `run-keeps`, `run-grows`, `never-reused` [READ S2/keep.sl:109-153]. [RAN] the proof runs listed in section 6
   all exit 0.
7. **Renaming is the expensive obligation: 413 non-blank lines, 2.6 times the spec.** [RAN] `grep -c .` on
   `ren.sl` (234), `ren-small.sl` (63), `ren-grow.sl` (56), and `ren-online.sl` (60). It needed no change to any rule.
   It is proved only for two heaps of the same shape; relating a compile-time heap to a run-time heap of a
   different layout would need a different heap relation [INFERENCE, section 6.2].
8. **The deriving functions have six kinds of stuck outcome**: no such variable, no such function, a dangling
   address, a write to an immediate, no such field, and no branch. [RAN] `$B $SPEC $FNS ex-lib.sl ex-stuck.sl`
   shows five of them and out-of-fuel; I wrote no program that reaches the dangling address (section 4.3).
   Two would-be stuck states are refuted by carried evidence instead (section 4.3).
9. **slc's compile-time store is already a mutating heap with a counter allocator.** It proves that references
   stay valid as the store grows; it proves nothing that relates the store after a write to the store before
   (section 8). **Both answers of the equality test on equal numbers are observed today**: the two interpreters
   say "no" and the two compiled programs say "yes" for one program [RAN, section 8], so the test has to be
   nondeterministic in the spec, as §67 has it.
10. **DESIGN.md is silent on how an address is chosen.** [RAN] `grep -n -i "address" /home/user/sleight/DESIGN.md`
    matches line 1701 only; `grep -n -i "pointer"` matches lines 1462, 1488, 1489, 1803, 2632, and 2689;
    `grep -n -i "allocat\|fresh block\|fresh copy\|fresh cell"` matches lines 1735, 1773, 1837, and 2719. None of
    those lines speaks of order, arithmetic, or reuse.

---

## 1. The model language

[READ S2/code.sl:1-24] The whole syntax:

```scheme
(def-adts
  ((Atom : -> Type)
    enum
    (many AVar : (many (Nat) i) -> (Atom))
    (many AImm : (many (Nat) n) -> (Atom)))
  ((Instr : -> Type)
    enum
    (many IAtom : (many (Atom) a) -> (Instr))
    (many ICon : (many (Nat) tag) (many (List (Atom)) args) -> (Instr))
    (many IWrite : (many (Atom) target) (many (Nat) i) (many (Atom) v) -> (Instr))
    (many ICopy : (many (Atom) target) (many (Nat) i) (many (Atom) v) -> (Instr))
    (many ISame : (many (Atom) a) (many (Atom) b) -> (Instr)))
  ((Code : -> Type)
    enum
    (many CDo : (many (Instr) i) -> (Code))
    (many CLet : (many (Code) rhs) (many (Code) body) -> (Code))
    (many CMatch : (many (Atom) scrut) (many (List (Code)) blocks) (many (List (Code)) imms) -> (Code))
    (many CCall : (many (Nat) f) (many (List (Atom)) args) -> (Code)))
  ((Label : -> Type)
    enum
    (many LTau : -> (Label))
    (many LAddr : (many (Nat) a) -> (Label))
    (many LYes : -> (Label))
    (many LNo : -> (Label))))
```

Design choices, all mine:

- **Operands are atoms** (a variable or an immediate constant), so no instruction holds code and code nests
  only through `CLet` and the branches of `CMatch`. The basis I took is [QUOTE DESIGN.md:655-656 §15] "Every argument to a constructor, a function or a cell behaves
  as if it were first bound to an anonymous variable." The handoff records that the order among the
  sub-expressions of one form is an open question
  [READ /tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/handoff.md:34]; this
  model has no such order to choose because its syntax has no nested operands. [INFERENCE] That postpones the question to whatever translates
  source into this form.
- **Variables are de Bruijn indices into a list of words**; index 0 is the newest binding. A `CLet` pushes one
  word; a `CMatch` on a block pushes its fields, first field at index 0; a call starts from the argument words
  alone, first argument at index 0, since functions are top-level and closed.
- **Words**: `(WImm n)` or `(WAddr a)`; a **block** is a tag and a list of words; a **heap** is a list of
  address and block pairs [READ S2/heap.sl:1-12].
- **A match** reads one word. An immediate `n` selects `imms[n]` and binds nothing; an address selects
  `blocks[tag]` of the block it names and binds the fields [READ S2/code.sl:66-72]. Both tables are indexed by
  position, after [QUOTE DESIGN.md:1467-1468 §33] "A block's tag counts only the constructors with fields." and
  [QUOTE DESIGN.md:1470-1472 §33] "A value with no non-erased field is the word of the `Nat` of its position among
  the fieldless non-phantom constructors when its type is tagged".
- **`IWrite`** stores one word into one field of an existing block and returns that block's address; **`ICopy`**
  allocates a fresh block that is the old one with one field replaced and returns the new address. They stand for
  the two cases of [QUOTE DESIGN.md:1752-1758 §37] "At `unique` the form takes `u` at unique and yields the same
  cell under the new type, at `u`. This is a physical store into memory that the cell's eventual invocation
  re-creates; it does no usage accounting of its own. At `many` the form uses `u` at many and copies: the result
  is a fresh block holding the old words with the written slots replaced, at unique and at nothing." Neither can
  change a block's tag or its number of fields, after [QUOTE DESIGN.md:1750-1751 §37] "`C` must be the cell's own
  constructor, canonically."
- **`ISame`** is the word-equality test. Its result is the immediate 1 for yes and 0 for no. [INFERENCE] That is
  what `slot-eq`'s result would be under §33, since `ESome` and `ENone` have no non-erased field
  [READ /home/user/sleight/lib/prelude.sl:1263-1266] and `ENone` is declared first.
- **One result word per piece of code.** DESIGN.md has [QUOTE DESIGN.md:1074 §26] "A function returns zero or more
  values." Not modelled.
- **No closures.** Section 9.4 says what they would add.
- **A label** records the one choice a step may make: the address an allocation took, or the answer the equality
  test gave. `LTau` is a step with no choice.

---

## 2. The relations

### 2.1 The heap: fresh, lookup, update, allocate

[READ S2/heap.sl:14-33]

```scheme
(def-adts
  ((Fresh : ((Heap) h) ((Nat) a) -> Type)
    enum
    (many FreshNil : (erased (Nat) a) -> (Fresh (HNil) a))
    (many FreshCons : (erased (Nat) a) (erased (Nat) b) (erased (Block) other) (erased (Heap) rest)
       (erased (Neq a b) n) (erased (Fresh rest a) p) -> (Fresh (HCons b other rest) a)))
  ((Lookup : ((Heap) h) ((Nat) a) ((Block) blk) -> Type)
    enum
    (many LkHere : (erased (Nat) a) (erased (Block) blk) (erased (Heap) rest) -> (Lookup (HCons a blk rest) a blk))
    (many LkThere : (erased (Nat) a) (erased (Nat) b) (erased (Block) blk) (erased (Block) other) (erased (Heap) rest)
       (erased (Neq a b) n) (erased (Lookup rest a blk) p) -> (Lookup (HCons b other rest) a blk)))
  ((Update : ((Heap) h) ((Nat) a) ((Block) blk) ((Heap) h2) -> Type)
    enum
    (many UpHere : (erased (Nat) a) (erased (Block) old) (erased (Block) blk) (erased (Heap) rest)
       -> (Update (HCons a old rest) a blk (HCons a blk rest)))
    (many UpThere : (erased (Nat) a) (erased (Nat) b) (erased (Block) blk) (erased (Block) other) (erased (Heap) rest) (erased (Heap) rest2)
       (erased (Neq a b) n) (erased (Update rest a blk rest2) p) -> (Update (HCons b other rest) a blk (HCons b other rest2))))
  ((Alloc : ((Heap) h) ((Nat) a) ((Block) blk) ((Heap) h2) -> Type)
    enum
    (many MkAlloc : (erased (Heap) h) (erased (Nat) a) (erased (Block) blk) (erased (Fresh h a) f) -> (Alloc h a blk (HCons a blk h)))))
```

- Allocation is nondeterministic: `MkAlloc` accepts **any** `a` with `(Fresh h a)`.
- An address is a `Nat`. A rule relates two addresses in one of two ways only: it names them by one variable
  (they are the same address), or it has the premise `(Neq a b)`.
  [RAN] `grep -n "Lt\|Succ\|Add \|nat-\|Zero" heap.sl code.sl big.sl small.sl` matches `code.sl:63` and `code.sl:65`
  only, which are the immediates 1 and 0 that `ISame` answers. So no rule adds to, or orders, an address.
  `Neq` itself is defined from the prelude's `Lt` [READ /home/user/sleight/mini/base.sl:5-8], so the abstraction
  is by convention in the syntax; the theorem `ren-run` (section 6.2) is what shows no rule depends on the order,
  and the instance in `corollary.sl` uses an order-reversing renaming (7 to 100, 3 to 200).
- `Lookup` and `Update` skip an entry only with evidence that its address differs, so each is a function of its
  inputs with no assumption on the heap (`lookup-fn`, `update-fn` [READ S2/det.sl:26-48]).

### 2.2 One instruction against a heap, and what a match reads

[READ S2/code.sl:42-72]

```scheme
(def-adts
  ((Patched : ((Heap) h) ((List (Word)) env) ((Atom) a) ((Nat) i) ((Atom) b) ((Nat) p) ((Block) blk) -> Type)
    enum
    (many MkPatched : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
       (erased (Nat) p) (erased (Word) w) (erased (Nat) tag) (erased (List (Word)) fs) (erased (List (Word)) fs2)
       (erased (AtomVal env a (WAddr p)) pa) (erased (AtomVal env b w) pb) (erased (Lookup h p (MkBlock tag fs)) lk)
       (erased (SetNth (Word) fs i w fs2) st) -> (Patched h env a i b p (MkBlock tag fs2))))
  ((Prim : ((Heap) h) ((List (Word)) env) ((Instr) i) ((Label) l) ((Heap) h2) ((Word) w) -> Type)
    enum
    (many PAtom : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Word) w)
       (erased (AtomVal env a w) p) -> (Prim h env (IAtom a) (LTau) h w))
    (many PCon : (erased (Heap) h) (erased (List (Word)) env) (erased (Nat) tag) (erased (List (Atom)) args)
       (erased (List (Word)) ws) (erased (Nat) p) (erased (Heap) h2)
       (erased (AtomVals env args ws) pa) (erased (Alloc h p (MkBlock tag ws) h2) al) -> (Prim h env (ICon tag args) (LAddr p) h2 (WAddr p)))
    (many PWrite : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
       (erased (Nat) p) (erased (Block) blk) (erased (Heap) h2)
       (erased (Patched h env a i b p blk) pt) (erased (Update h p blk h2) up) -> (Prim h env (IWrite a i b) (LTau) h2 (WAddr p)))
    (many PCopy : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
       (erased (Nat) p) (erased (Block) blk) (erased (Nat) q) (erased (Heap) h2)
       (erased (Patched h env a i b p blk) pt) (erased (Alloc h q blk h2) al) -> (Prim h env (ICopy a i b) (LAddr q) h2 (WAddr q)))
    (many PSameYes : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Atom) b) (erased (Word) w)
       (erased (AtomVal env a w) pa) (erased (AtomVal env b w) pb) -> (Prim h env (ISame a b) (LYes) h (WImm (Succ (Zero)))))
    (many PSameNo : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Atom) b) (erased (Word) w1) (erased (Word) w2)
       (erased (AtomVal env a w1) pa) (erased (AtomVal env b w2) pb) -> (Prim h env (ISame a b) (LNo) h (WImm (Zero)))))
  ((Select : ((Heap) h) ((Word) w) ((List (Code)) blocks) ((List (Code)) imms) ((Code) body) ((List (Word)) fields) -> Type)
    enum
    (many SelImm : (erased (Heap) h) (erased (Nat) n) (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Code) body)
       (erased (Nth (Code) imms n body) br) -> (Select h (WImm n) blocks imms body (Nil (Word))))
    (many SelBlock : (erased (Heap) h) (erased (Nat) p) (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Code) body)
       (erased (Nat) tag) (erased (List (Word)) fs)
       (erased (Lookup h p (MkBlock tag fs)) lk) (erased (Nth (Code) blocks tag body) br) -> (Select h (WAddr p) blocks imms body fs))))
```

- `PWrite` and `PCopy` share `Patched` ("the block at `a` with field `i` replaced by `b`'s word"); they differ in
  one premise, `Update` against `Alloc`.
- `PSameYes` needs both atoms to evaluate to **one** word `w`; `PSameNo` needs nothing. So equal words may answer
  yes or no, and unequal words can only answer no. This is my reading of [QUOTE DESIGN.md:3044-3046 §67] "`ESome`
  proves that `a` and `b` hold one word (§38). `ENone` proves nothing, so an implementation may always answer it,
  and which one a call answers may differ between runs."
- Helper relations `AtomVal`, `AtomVals`, and `Cat` (list append, for binding fields) are at
  [READ S2/code.sl:26-40]. `Nth` and `SetNth` are the prelude's
  [READ /home/user/sleight/lib/prelude.sl:1286-1297].

### 2.3 S-big: big-step with a threaded heap

[READ S2/big.sl:1-25] The shape is `(Run fns h env c ch h2 w)`: one more index than the brief's
`(Run fns heap env code heap2 words)`, namely `ch`, the tree of choices the run made, and one result word in place
of several.

```scheme
(def-adts
  ((Choices : -> Type)
    enum
    (many ChOne : (many (Label) l) -> (Choices))
    (many ChSeq : (many (Choices) first) (many (Choices) rest) -> (Choices))))

(def-adts
  ((Run : ((List (Code)) fns) ((Heap) h) ((List (Word)) env) ((Code) c) ((Choices) ch) ((Heap) h2) ((Word) w) -> Type)
    enum
    (many RunDo : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i)
       (erased (Label) l) (erased (Heap) h2) (erased (Word) w)
       (erased (Prim h env i l h2 w) p) -> (Run fns h env (CDo i) (ChOne l) h2 w))
    (many RunLet : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) rhs) (erased (Code) body)
       (erased (Choices) ch1) (erased (Heap) h1) (erased (Word) w1) (erased (Choices) ch2) (erased (Heap) h2) (erased (Word) w2)
       (erased (Run fns h env rhs ch1 h1 w1) p) (erased (Run fns h1 (Cons (Word) w1 env) body ch2 h2 w2) q)
       -> (Run fns h env (CLet rhs body) (ChSeq ch1 ch2) h2 w2))
    (many RunMatch : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a)
       (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Word) w) (erased (Code) body) (erased (List (Word)) fs)
       (erased (List (Word)) env2) (erased (Choices) ch) (erased (Heap) h2) (erased (Word) w2)
       (erased (AtomVal env a w) pa) (erased (Select h w blocks imms body fs) sel) (erased (Cat fs env env2) ct)
       (erased (Run fns h env2 body ch h2 w2) q) -> (Run fns h env (CMatch a blocks imms) ch h2 w2))
    (many RunCall : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Nat) f) (erased (List (Atom)) args)
       (erased (Code) body) (erased (List (Word)) ws) (erased (Choices) ch) (erased (Heap) h2) (erased (Word) w)
       (erased (Nth (Code) fns f body) pf) (erased (AtomVals env args ws) pa) (erased (Run fns h ws body ch h2 w) q)
       -> (Run fns h env (CCall f args) ch h2 w))))
```

Only `RunLet` chains two runs through a heap in the middle: `h` to `h1` to `h2`. The other three rules hand the
heap to `Prim` or to one sub-run.

### 2.4 S-small: an abstract machine with an explicit stack

[READ S2/small.sl:1-35] A machine state is a heap and a `Control`; a `Step` carries a label.

```scheme
(def-adts
  ((Stack : -> Type)
    enum
    (many KNil : -> (Stack))
    (many KLet : (many (List (Word)) env) (many (Code) body) (many (Stack) rest) -> (Stack)))
  ((Control : -> Type)
    enum
    (many KRun : (many (List (Word)) env) (many (Code) c) (many (Stack) k) -> (Control))
    (many KRet : (many (Word) w) (many (Stack) k) -> (Control))))

(def-adts
  ((Step : ((List (Code)) fns) ((Heap) h) ((Control) c) ((Label) l) ((Heap) h2) ((Control) c2) -> Type)
    enum
    (many StDo : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i) (erased (Stack) k)
       (erased (Label) l) (erased (Heap) h2) (erased (Word) w)
       (erased (Prim h env i l h2 w) p) -> (Step fns h (KRun env (CDo i) k) l h2 (KRet w k)))
    (many StLet : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) rhs) (erased (Code) body) (erased (Stack) k)
       -> (Step fns h (KRun env (CLet rhs body) k) (LTau) h (KRun env rhs (KLet env body k))))
    (many StRet : (erased (List (Code)) fns) (erased (Heap) h) (erased (Word) w) (erased (List (Word)) env) (erased (Code) body) (erased (Stack) k)
       -> (Step fns h (KRet w (KLet env body k)) (LTau) h (KRun (Cons (Word) w env) body k)))
    (many StMatch : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a)
       (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Stack) k)
       (erased (Word) w) (erased (Code) body) (erased (List (Word)) fs) (erased (List (Word)) env2)
       (erased (AtomVal env a w) pa) (erased (Select h w blocks imms body fs) sel) (erased (Cat fs env env2) ct)
       -> (Step fns h (KRun env (CMatch a blocks imms) k) (LTau) h (KRun env2 body k)))
    (many StCall : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Nat) f) (erased (List (Atom)) args) (erased (Stack) k)
       (erased (Code) body) (erased (List (Word)) ws)
       (erased (Nth (Code) fns f body) pf) (erased (AtomVals env args ws) pa)
       -> (Step fns h (KRun env (CCall f args) k) (LTau) h (KRun ws body k))))
  ((Steps : ((List (Code)) fns) ((Heap) h) ((Control) c) ((List (Label)) ls) ((Heap) h2) ((Control) c2) -> Type)
    enum
    (many StepsNil : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) -> (Steps fns h c (Nil (Label)) h c))
    (many StepsCons : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (erased (Label) l) (erased (Heap) h1) (erased (Control) c1)
       (erased (List (Label)) ls) (erased (Heap) h2) (erased (Control) c2)
       (erased (Step fns h c l h1 c1) p) (erased (Steps fns h1 c1 ls h2 c2) q) -> (Steps fns h c (Cons (Label) l ls) h2 c2))))
```

Only `CLet` pushes a frame. A call replaces the control and pushes nothing, so a call in the final position of a
function body is a jump. A finished run is a state `(KRet w (KNil))`.

---

## 3. Size: relation versus deriving function

[RAN] `for f in ...; do printf ... $(grep -c . $f) $(wc -c < $f) ...; done` over the files of `S2/`:

| Part | File | Non-blank lines | Bytes | Rules or functions |
|---|---|---|---|---|
| Spec, shared | `heap.sl` | 32 | 1810 | 3 data types; `Fresh` 2, `Lookup` 2, `Update` 2, `Alloc` 1 |
| Spec, shared | `code.sl` | 70 | 5117 | 4 data types; `AtomVal` 2, `AtomVals` 2, `Cat` 2, `Patched` 1, `Prim` 6, `Select` 2 |
| Spec, S-big | `big.sl` | 24 | 1967 | `Choices` (data); `Run` 4 |
| Spec, S-small | `small.sl` | 34 | 2703 | 2 data types; `Step` 5, `Steps` 2 |
| **Spec total** | | **160** | **11597** | 22 shared rules, 4 for S-big, 7 for S-small |
| Deriving, shared | `heap-fn.sl` | 44 | 3177 | 6 functions |
| Deriving, shared | `prim-fn.sl` | 121 | 8312 | 8 functions, 7 result types |
| Deriving, S-big | `run-fn.sl` | 36 | 2655 | `run` |
| Deriving, S-small | `step-fn.sl` | 47 | 3452 | `step`, `steps` |
| **Deriving total** | | **248** | **17596** | |
| Proofs | `det.sl` | 177 | 10641 | 13 lemmas |
| Proofs | `keep.sl` | 138 | 10534 | 21 lemmas |
| Proofs | `agree.sl` | 36 | 2683 | 2 lemmas |
| Proofs | `ren.sl`, `ren-small.sl`, `ren-grow.sl`, `ren-online.sl` | 413 | 31089 | 34 lemmas; 14 type declarations (the renaming and 13 relations) |
| Proofs | `corollary.sl` | 39 | 2836 | 1 lemma and 1 worked instance |
| Experiment | `abs.sl` | 33 | 2723 | section 9.3 |

Lines are long (the longest is 168 characters; [RAN] `awk '{ if (length($0)>m) m=length($0) } END { print m }' FILE`
per file), so bytes are the fairer measure: the deriving functions are about 1.5 times the spec.

What makes the text large and awkward, as I see it [INFERENCE from the files]:

- A rule lists every variable it mentions as an erased field. `RunMatch` has 17 fields, of which 4 are premises
  [READ S2/big.sl:17-21].
- Proofs match those fields by position: `((RunMatch _ _ _ a blocks imms v1 body1 fs1 env1 _ _ _ pa1 sel1 ct1 q1) ...)`
  [READ S2/det.sl:125]. A miscounted `_` is caught by the checker only when the types of the two fields differ.
- Each decided relation needs its own result type, because a type constructor cannot be partly applied:
  [RAN] `$B $SPEC neg/generic-dec-bad.sl` printed
  ``neg/generic-dec-bad.sl:7:103: error: `AtomVal` expects 3 arguments, got 2: expected `((List (Word)) env) ((Atom) a) ((Word) w)` ``.
  `prim-fn.sl` declares 7 such types with 14 constructors between them [READ S2/prim-fn.sl:16-47], and the
  other three function files declare 4 more [READ S2/heap-fn.sl:2-5, S2/run-fn.sl:2-7, S2/step-fn.sl:2-14].

---

## 4. The deriving functions

### 4.1 What they return

- `prim` [READ S2/prim-fn.sl:106-130] runs one instruction and returns the new heap, the new counter, the
  invariant for them, the result word, and an erased `(Prim h env i l h2 w)`.
- `run` [READ S2/run-fn.sl:9-37] burns fuel and returns `RanOk` with the same data and an erased
  `(Run fns h env c ch h2 w)`, or `RanHalt` with `(OutOfFuel)` or `(Stuck why)`.
- `step` [READ S2/step-fn.sl:16-38] takes **no fuel** and makes no recursive call of its own; it returns the next
  state with an erased `(Step fns h c l h2 c2)`, or `StepFinal` when the state is `(KRet w (KNil))`, or
  `StepStuck why`. The functions it calls recurse on a list each.
- `steps` [READ S2/step-fn.sl:40-49] loops `step` on fuel and returns an erased
  `(Steps fns h c ls h2 (KRet w (KNil)))` and the number of steps taken.

### 4.2 How the nondeterminism is resolved

- **Addresses: a counter.** The next address is the counter, and the counter then goes up by one.
  The functions carry `(erased (Below h next) inv)`: every address in `h` is below `next`
  [READ S2/heap-fn.sl:22-27]. From it `below-fresh` gives `(Fresh h next)` [READ S2/heap-fn.sl:29-32], so `alloc`
  [READ S2/heap-fn.sl:47-51] never tests freshness and has no failing case.
- **Equality: "yes" exactly when the two words are identical**, by `word-dec` [READ S2/prim-fn.sl:84-91,
  125-130]. Two immediates with the same number count as identical.

### 4.3 Stuck states: every place an outcome is neither a result nor out-of-fuel

[RAN] `grep -n "(NoVar)\|(NoFn)\|(Dangling)\|(NotBlock)\|(NoField)\|(NoBranch)" heap-fn.sl prim-fn.sl run-fn.sl step-fn.sl`
gave the sites below (the rest of the functions only pass a stuck outcome on).

| Kind | Meaning | Sites | Could an intrinsic formulation refute it? [INFERENCE] |
|---|---|---|---|
| `NoVar` | a variable index beyond the environment | `prim-fn.sl:75, 76, 110, 113, 126, 127`; `run-fn.sl:24, 33`; `step-fn.sl:31, 37` | Yes, cheaply: index code by the length of its environment and give `AVar` a bound proof. |
| `NoFn` | a call to an index beyond the function table | `run-fn.sl:32`; `step-fn.sl:36` | Yes, cheaply: a bound proof in `CCall` against the table's length. |
| `Dangling` | an address the heap does not hold | `prim-fn.sl:78, 100` | Yes, by a closure invariant on heap, environment, and stack ("every address held is in the heap"), or by references that carry their own validity, which is what slc's store does (section 8). |
| `NotBlock` | `IWrite` or `ICopy` aimed at an immediate | `prim-fn.sl:77` | Only with types for words: the model has none. |
| `NoField` | a field index beyond the block | `prim-fn.sl:81` | Needs a table from tag to size and a heap invariant that blocks have that size. `run-keeps` (section 6.3) already shows no rule changes a block's tag or size. |
| `NoBranch` | no branch for the tag or the immediate | `prim-fn.sl:97, 103` | Only with types: coverage is a fact about the scrutinee's type. |

[RAN] `$B $SPEC $FNS ex-lib.sl ex-stuck.sl` printed (first of each pair from `run`, second from `steps`):

```
(Cons _ (MkPair _ _ (Stuck $ NoVar) $ Stuck $ NoVar) $ Cons _ (MkPair _ _ (Stuck $ NoFn) $ Stuck $ NoFn) $ Cons _ (MkPair _ _ (Stuck $ NotBlock) $ Stuck $ NotBlock) $ Cons _ (MkPair _ _ (Stuck $ NoField) $ Stuck $ NoField) $ Cons _ (MkPair _ _ (Stuck $ NoBranch) $ Stuck $ NoBranch) $ Cons _ (MkPair _ _ (OutOfFuel) $ OutOfFuel) $ Nil _)
```

The last program's one function has a body that is a call of itself [READ S2/ex-stuck.sl:12, 19], so
[INFERENCE] the model language has programs that never finish; the run shows only that 50 units of fuel were
not enough.
I wrote no program that reaches `Dangling`. [INFERENCE] None exists from an empty heap and environment, because
every address a rule hands out is one it has just allocated; that claim is the closure invariant, which I did not
state or prove.

Two outcomes that would otherwise be stuck are **refuted by evidence the function carries**:

- "the allocated address is already in use": refuted by `Below` (4.2).
- "update of an address that is not there": `update` takes the `Lookup` evidence the caller already has, and its
  two impossible cases are absurd branches [READ S2/heap-fn.sl:14-20].

[INFERENCE] The three kinds that need types are the hard ones. The stripped code has no types left, so refuting
them needs an invariant that relates words and blocks to the types of the source program, kept true by every
rule. `IWrite` stands for a write that §37 says yields "the same cell under the new type" (quoted in section 1),
so that invariant cannot simply say "a block's type never changes"; it has to use the fact that the written cell
is `unique`. I did not attempt it. A stuck outcome here carries no evidence that no rule applies. The previous
session proposed, for programs the compiler rejects,
[QUOTE /tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/handoff.md:40] "a
derivation of a positive `Fails` relation"; the same idea here would be a relation that says a state is stuck.

---

## 5. Examples

Each prints a pair: `run`'s result (S-big), then `steps`' result (S-small). In `RanOk` the printed fields are the
final heap, the counter, the result word; in `StepsOk` also the number of steps. `_` is an erased field.

### (a) Overwrite in place, read back through the original pointer

[READ S2/ex-a.sl:1-9] The program builds `l3 = Cons 30 Nil`, `l2 = Cons 20 l3`, `l1 = Cons 10 l2`, then writes 99
into field 0 of the block `l2` names, then matches `l1`, matches its tail, and returns that tail's head. The read
goes through `l1`, built before the write; the write goes through the variable `l2`.

[RAN] `$B $SPEC $FNS ex-lib.sl ex-a.sl`:

```
(MkPair _ _ (RanOk _ _ _ _ (HCons 2 (MkBlock 0 $ Cons _ (WImm 10) $ Cons _ (WAddr 1) $ Nil _) $ HCons 1 (MkBlock 0 $ Cons _ (WImm 99) $ Cons _ (WAddr 0) $ Nil _) $ HCons 0 (MkBlock 0 $ Cons _ (WImm 30) $ Cons _ (WImm 0) $ Nil _) $ HNil) 3 _ (WImm 99) _ _) $ StepsOk _ _ _ (HCons 2 (MkBlock 0 $ Cons _ (WImm 10) $ Cons _ (WAddr 1) $ Nil _) $ HCons 1 (MkBlock 0 $ Cons _ (WImm 99) $ Cons _ (WAddr 0) $ Nil _) $ HCons 0 (MkBlock 0 $ Cons _ (WImm 30) $ Cons _ (WImm 0) $ Nil _) $ HNil) 3 _ (WImm 99) 15 _ _)
```

Result `(WImm 99)` both ways. The relation assumes nothing about uniqueness: block 1 changed, and the pointer to
it inside block 2 sees the change.

### (b) Destination-passing append, after DESIGN.md §61

[READ S2/ex-b.sl:1-29] Function 0, `append-into(cell, h, xs, ys)`: on `Nil`, store `h` and `ys` into `cell`; on
`Cons hd tl`, allocate `next` with two words of 0, store `h` then `next` into `cell`, and call
`append-into(next, hd, tl, ys)` as the last thing it does. Function 1, `append-list(xs, ys)`: on `Nil` return
`ys`; on `Cons hd tl` allocate `cell`, call `append-into(cell, hd, tl, ys)`, and return its own `cell`.
In §61 the helper's result is `at cell`; the model's function returns a word nobody uses, and the caller uses
its own `cell`, after [QUOTE DESIGN.md:1659-1663 §36] "An `at` return is absent from the physical values of a
call. A `let` binds it like any return, and the elaborator supplies its word from a non-erased entry in the same
slot: the caller's own binder for the argument the promise names".

[RAN] `$B $SPEC $FNS ex-lib.sl ex-b.sl` (the first component decodes the result as a list of numbers):

```
(MkPair _ _ (MkPair _ _ (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Nil _) $ RanOk _ _ _ _ (HCons 4 (MkBlock 0 $ Cons _ (WImm 2) $ Cons _ (WAddr 2) $ Nil _) $ HCons 3 (MkBlock 0 $ Cons _ (WImm 1) $ Cons _ (WAddr 4) $ Nil _) $ HCons 2 (MkBlock 0 $ Cons _ (WImm 3) $ Cons _ (WImm 0) $ Nil _) $ HCons 1 (MkBlock 0 $ Cons _ (WImm 1) $ Cons _ (WAddr 0) $ Nil _) $ HCons 0 (MkBlock 0 $ Cons _ (WImm 2) $ Cons _ (WImm 0) $ Nil _) $ HNil) 5 _ (WAddr 3) _ _) $ StepsOk _ _ _ (HCons 4 (MkBlock 0 $ Cons _ (WImm 2) $ Cons _ (WAddr 2) $ Nil _) $ HCons 3 (MkBlock 0 $ Cons _ (WImm 1) $ Cons _ (WAddr 4) $ Nil _) $ HCons 2 (MkBlock 0 $ Cons _ (WImm 3) $ Cons _ (WImm 0) $ Nil _) $ HCons 1 (MkBlock 0 $ Cons _ (WImm 1) $ Cons _ (WAddr 0) $ Nil _) $ HCons 0 (MkBlock 0 $ Cons _ (WImm 2) $ Cons _ (WImm 0) $ Nil _) $ HNil) 5 _ (WAddr 3) 34 _ _)
```

Blocks 3 and 4 are the new cells, filled after they were allocated; block 4's tail is `(WAddr 2)`, the shared
`ys`; blocks 0 and 1, the old `xs`, are untouched.

**Constant stack.** [RAN] `$B $SPEC $FNS ex-lib.sl ex-b.sl ex-depth.sl` runs the same two functions on lists of
2, 8, and 32 elements and prints, for each, the deepest stack the small-step machine reached and the steps it took:

```
(Cons _ (MkPair _ _ 2 34) $ Cons _ (MkPair _ _ 2 118) $ Cons _ (MkPair _ _ 2 454) $ Nil _)
```

Depth 2 at every length; 14 steps per extra element. Compare [QUOTE DESIGN.md:2718-2719 §61] "Per element: one
allocation, two stores, constant stack."

### (c) Word equality

[READ S2/ex-c.sl:1-7] Allocate `a = Cons 7 Nil` and `b = Cons 7 Nil`, compute `same(a, b)` and `same(a, a)`, and
return a block (tag 1) holding the two answers.

[RAN] `$B $SPEC $FNS ex-lib.sl ex-c.sl`:

```
(MkPair _ _ (RanOk _ _ _ _ (HCons 2 (MkBlock 1 $ Cons _ (WImm 0) $ Cons _ (WImm 1) $ Nil _) $ HCons 1 (MkBlock 0 $ Cons _ (WImm 7) $ Cons _ (WImm 0) $ Nil _) $ HCons 0 (MkBlock 0 $ Cons _ (WImm 7) $ Cons _ (WImm 0) $ Nil _) $ HNil) 3 _ (WAddr 2) _ _) $ StepsOk _ _ _ (HCons 2 (MkBlock 1 $ Cons _ (WImm 0) $ Cons _ (WImm 1) $ Nil _) $ HCons 1 (MkBlock 0 $ Cons _ (WImm 7) $ Cons _ (WImm 0) $ Nil _) $ HCons 0 (MkBlock 0 $ Cons _ (WImm 7) $ Cons _ (WImm 0) $ Nil _) $ HNil) 3 _ (WAddr 2) 13 _ _)
```

Block 2 holds `(WImm 0)` then `(WImm 1)`: two separately allocated blocks with equal contents answer no, and one
block against itself answers yes, under the function's policy. Compare [QUOTE DESIGN.md:1697-1698 §36] "two
separately built cells with equal contents are `is`-equal and are two blocks."

**The relation itself allows more than the function chooses.** [RAN] `$B $SPEC ex-spec.sl` exits 0; that file
[READ S2/ex-spec.sl:1-8] builds by hand, for one word compared with itself, both a derivation with label `(LYes)`
and result 1 and a derivation with label `(LNo)` and result 0. A "yes" on two different words is refused:
[RAN] `$B $SPEC neg/same-yes-distinct-bad.sl` exits 1 with

```
neg/same-yes-distinct-bad.sl:5:75: error: argument 7, `pb`, of `PSameYes`: type mismatch: expected `(AtomVal (Cons (Word) (WAddr 5) (Cons (Word) (WAddr 6) (Nil (Word)))) (AVar (Succ (Zero))) (WAddr 5))`, got `(AtomVal (Cons (Word) (WAddr 5) (Cons (Word) (WAddr 6) (Nil (Word)))) (AVar (Succ (Zero))) (WAddr 6))`
```

and in general `same-yes-sound` [READ S2/det.sl:184-189] proves that a `(LYes)` step implies the two atoms'
words are equal.

### (d) Copy-then-write, not asked for

[RAN] `$B $SPEC $FNS ex-lib.sl ex-d.sl` allocates `a = Cons 1 Nil`, copies it with field 0 replaced by 99, and
returns a block holding both heads; it printed a final heap whose block 0 is
`(MkBlock 0 $ Cons _ (WImm 1) $ Cons _ (WImm 0) $ Nil _)`, block 1 is
`(MkBlock 0 $ Cons _ (WImm 99) $ Cons _ (WImm 0) $ Nil _)`, and block 2 is
`(MkBlock 1 $ Cons _ (WImm 1) $ Cons _ (WImm 99) $ Nil _)`. The old block is unchanged.

### (e) An allocation order no counter would produce

[READ S2/ex-spec.sl:10-28] A hand-built `Run` derivation for "allocate a block, then allocate a block that points
to it" in which the first allocation takes address 7 and the second takes address 3. [RAN] `$B $SPEC ex-spec.sl`
exits 0. My attempt to take 7 twice is refused: [RAN] `$B $SPEC neg/reuse-address-bad.sl` exits 1 with
``neg/reuse-address-bad.sl:4:56: error: `prove-literal-lt`: 7 is not below 7``. The attempt needs `(Neq 7 7)`
for `Fresh`, and tried to get it from `(Lt 7 7)`. The general statement is `alloc-not-live` (section 6.3).

---

## 6. Proof obligations

Every lemma below is an `erased` Sleight function whose signature is the statement. "Proved" means the file
type-checks under both implementations (finding 1). Statements only are marked **stated**.

### 6.1 (a) Determinism up to the choices

**What is even statable.** Without fixing the choices the claim is false: `ex-spec.sl` holds two derivations of
one instruction on one state with different results. The checker also refuses the proof:
[RAN] `$B $SPEC neg/det-nolabel-bad.sl` exits 1 with

```
neg/det-nolabel-bad.sl:7:7: error: this `let-match` is missing a branch for the following unrefuted constructor:
code.sl:64:5: note: value constructor `PSameNo`, which is declared here
```

So the choices have to be named in the statement. I put them in the relations: a `Label` on `Prim` and `Step`,
a `Choices` tree on `Run`. [QUOTE DESIGN.md:419 §9] "The elaborated form of a type never contains a function
call", so "the trace of this derivation" cannot be computed inside a type; it is either an index, as here, or a
second relation indexed by the derivation. I did not try the second.

**Proved** [RAN] `$B $SPEC det.sl` exits 0:

| Lemma | Statement | Where |
|---|---|---|
| `prim-det` | `(Prim h env i l h1 w1)` and `(Prim h env i l h2 w2)` give `h1 = h2` and `w1 = w2` | `S2/det.sl:68-96` |
| `run-det` | `(Run fns h env c ch h1 w1)` and `(Run fns h env c ch h2 w2)` give `h1 = h2` and `w1 = w2` | `S2/det.sl:111-137` |
| `step-det` | `(Step fns h c l h1 c1)` and `(Step fns h c l h2 c2)` give `h1 = h2` and `c1 = c2` | `S2/det.sl:139-167` |
| `steps-det` | the same for `Steps` with one list of labels | `S2/det.sl:169-182` |
| `same-yes-sound` | a `(LYes)` step implies the two words are equal | `S2/det.sl:184-189` |

`run-det`'s signature in full:

```scheme
(def-fns _ $ (erased run-det : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) c) (erased (Choices) ch)
    (erased (Heap) h1 h2) (erased (Word) w1 w2)
    (subterm erased (Run fns h env c ch h1 w1) d1) (erased (Run fns h env c ch h2 w2) d2) ->
    (erased (Eq (Heap) h1 h2) eh) (erased (Eq (Word) w1 w2) ew))
```

It rests on 8 functionality lemmas, one per helper relation (`atomval-fn`, `atomvals-fn`, `cat-fn`, `lookup-fn`,
`update-fn`, `alloc-fn`, `patched-fn`, `select-fn`), and on `nth-fn` and `setnth-fn` from
`/home/user/sleight/std/list.sl` [READ /home/user/sleight/std/list.sl:14-19, 36-41].

**Also proved**, `det-up-to-renaming` [READ S2/corollary.sl:1-10]; [RAN] `$B $SPEC det.sl ren.sl corollary.sl`
exits 0: two runs of one program from one start whose choice trees correspond under a renaming (so the same
yes and no answers, and any addresses) end in heaps and words that correspond under that renaming.

### 6.2 (b) Invariance under renaming of addresses

**The renaming.** A list of address pairs, `Ren`, with a membership relation `RenA` that skips an entry only with
evidence that **both** components differ [READ S2/ren.sl:1-10]. That makes it a partial one-to-one map by
construction: `ren-fun` and `ren-inj` are proved from the definition, with no hypothesis [READ S2/ren.sl:41-59].
Dropping the evidence on the second component breaks `ren-inj`:
[RAN] `$B $SPEC neg/ren-onesided-bad.sl` exits 1 with
``neg/ren-onesided-bad.sl:56:59: error: argument 2, `n`, of `neq-irrefl`: type mismatch: expected `(Neq x x)`, got `(Neq b a)` ``.
Words, lists of words, blocks, heaps, labels, choice trees, stacks, and controls are related pointwise
[READ S2/ren.sl:11-39, S2/ren-small.sl:1-17]. **Two heaps are related only when they have the same shape**:
the same number of entries, in the same order, with related addresses and related blocks [READ S2/ren.sl:24-28].

**Form 1, a whole run, proved.** [RAN] `$B $SPEC keep.sl ren.sl ren-small.sl ren-grow.sl ren-online.sl` exits 0.

```scheme
(def-fns _ $ (erased ren-run : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (List (Word)) env env') (erased (Code) c)
    (erased (Choices) ch ch') (erased (Heap) h2) (erased (Word) w)
    (erased (RenH r h h') rh) (erased (RenWs r env env') re) (erased (RenCh r ch ch') rc) (subterm erased (Run fns h env c ch h2 w) d) ->
    (erased (Heap) h2') (erased (Word) w') (erased (Run fns h' env' c ch' h2' w') d') (erased (RenH r h2 h2') rh2) (erased (RenW r w w') rw))
```

Read: given a run with choices `ch`, and **any** choices `ch'` that are the image of `ch` under a one-to-one
renaming `r` that also relates the starting heaps and environments, a run with choices `ch'` exists and its final
heap and word are the images. Freshness of the second run's addresses is derived, not assumed (`ren-fresh`
[READ S2/ren.sl:135-141]). `ren-steps` is the same for S-small [READ S2/ren-small.sl:53-65].
A worked instance [READ S2/corollary.sl:12-40]: from the hand-built run that allocates 7 then 3, `ren-run` with
`r` = 7 to 100, 3 to 200 yields a run typed with choices `(ChSeq (ChOne (LAddr 100)) (ChOne (LAddr 200)))`.

The proof of the "yes" case uses that the renaming is functional (`renw-fun`). With that one line removed the
proof is refused: [RAN] `$B $SPEC neg/ren-nofun-bad.sl` exits 1 with
``neg/ren-nofun-bad.sl:205:68: error: argument 7, `pb`, of `PSameYes`: type mismatch: expected `(AtomVal env' b va)`, got `(AtomVal env' b vb)` ``.

**Form 2, one step at a time with a growing renaming, proved.** This is the form for two machines running side by
side, where the second machine's choice is not known in advance.

```scheme
(def-fns _ $ (erased sim-alloc : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (Control) c c') (erased (Nat) p q)
    (erased (Heap) h2) (erased (Control) c2)
    (erased (RenH r h h') rh) (erased (RenC r c c') rc) (erased (Tight r h h') t)
    (erased (Step fns h c (LAddr p) h2 c2) d) (erased (Fresh h' q) f') ->
    (erased (Heap) h2') (erased (Control) c2') (erased (Step fns h' c' (LAddr q) h2' c2') d')
    (erased (RenH (RCons p q r) h2 h2') rh2) (erased (RenC (RCons p q r) c2 c2') rc2) (erased (Tight (RCons p q r) h2 h2') t2))
```

Read: if the first machine allocates `p`, then for **any** `q` fresh in the second machine's heap, the second
machine can allocate `q`, and the states correspond under the renaming extended by the pair. `Tight` says every
pair of the renaming names a block in each heap [READ S2/ren-online.sl:1-6]; all three invariants come back, so
the lemma can be applied again. `sim-quiet` is the same for a step that allocates nothing
[READ S2/ren-online.sl:54-67].

**How painful.** Measured: 413 non-blank lines against 160 for the spec; 34 lemmas and 14 type declarations
(the renaming and 13 relations). Where the lines go:

- 4 lemmas about the renaming itself, and one "the image exists and is related" lemma per helper relation and
  per judgment, 13 of them, in `ren.sl`;
- for the growing form, one "still related after the renaming grows by a pair" lemma per related thing, 7 in
  `ren-grow.sl` (addresses, words, word lists, blocks, heaps, stacks, controls), and the `Tight` invariant with
  4 lemmas in `ren-online.sl`.

[INFERENCE] The pain is volume, not difficulty: each lemma is one structural induction. Three things would make
it worse in a real spec. (1) Every new component of the machine state that holds words needs its own relation
and its own "grows" lemma. (2) Closures would put words inside function values. (3) The same-shape heap relation
is enough to compare two runs of one program, since both allocate and write in the same order; it cannot relate
a compile-time heap to the run-time heap of an emitted program if that heap holds the blocks in another order,
or holds only some of them. For that the heap relation would have to be "for each pair of the renaming, both
heaps hold related blocks", and the lemmas that take `RenH` apart by cases (`ren-lookup`, `ren-fresh`,
`ren-update`, `ren-alloc`, `renh-grow`; [RAN] `grep -n "RenHCons\|RenHNil" ren*.sl` shows only these) would be
redone over frame laws for the heap. Nothing above those five lemmas mentions the heap's shape.

### 6.3 (c) Fresh stays fresh; a block keeps its address

**Proved** [RAN] `$B $SPEC keep.sl` exits 0:

| Lemma | Statement | Where |
|---|---|---|
| `run-keeps` | if `(Run fns h env c ch h2 w)` and `(Lookup h x b)` then some `b2` has `(Lookup h2 x b2)` and `(Shape b b2)`: same tag, same number of fields | `S2/keep.sl:119-129` |
| `prim-keeps`, `step-keeps` | the same for one instruction and one step | `S2/keep.sl:91-101`, `S2/ren-online.sl:15-23` |
| `run-grows`, `steps-grows` | an address fresh in the final heap was fresh in the starting heap | `S2/keep.sl:109-117, 140-144` |
| `never-reused` | if `(Steps fns h0 c0 ls h c)` and then a step allocates `p`, then `(Fresh h0 p)` | `S2/keep.sl:151-154` |
| `alloc-not-live` | `(Alloc h p blk h2)` and `(Lookup h p b)` together are absurd | `S2/keep.sl:156-159` |

`never-reused` is "no rule ever needs an address to be reused" in a positive form: the address a step allocates
was fresh in **every** earlier heap of the run, so it was never in use before.

**What in the relation guarantees a block keeps its address.** Three facts about the rules
[READ S2/code.sl:49-65, S2/heap.sl:25-33]:

1. only `PCon`, `PCopy`, and `PWrite` change the heap;
2. `PCon` and `PCopy` go through `Alloc`, which adds one entry at an address it requires to be `Fresh` and leaves
   every other entry as it was;
3. `PWrite` goes through `Update`, which replaces the block at an address already present and leaves the list of
   addresses unchanged, and through `Patched`, which keeps the tag and replaces one field by `SetNth`, which
   keeps the length.

There is no rule that removes an entry. [INFERENCE] That is why "not in the heap" and the handoff's "never taken
before" [QUOTE /tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/handoff.md:36]
"a step that allocates may take any address never taken before" coincide here; a spec with a rule that frees
blocks would need a history of taken addresses instead.

### 6.4 Agreement of the two styles

**Proved**, `big-small` [READ S2/agree.sl:9-37]; [RAN] `$B $SPEC agree.sl` exits 0: from
`(Run fns h env c ch h2 w)`, for any stack `k`, some labels `ls` have
`(Steps fns h (KRun env c k) ls h2 (KRet w k))`.

**Stated, not proved**, `small-big` [READ S2/stated.sl:3-7]; [RAN] `$B $SPEC stated.sl` exits 0, which checks only
that the statement is a well-formed type: from `(Steps fns h (KRun env c (KNil)) ls h2 (KRet w (KNil)))` some
`ch` has `(Run fns h env c ch h2 w)`. [INFERENCE] The proof needs a lemma that splits a step sequence at the
point where a pushed frame is popped; I did not write it.

### 6.5 Obligations I can name and did not state as types

[INFERENCE] each:

- **No stuck state from well-formed input**: needs the closure invariant and a typing invariant (4.3).
- **`IWrite` is unobservable when the written block has one reference**, the property that would justify reading
  `unique` as "update in place"; and the matching claim that `ICopy` and `IWrite` agree up to the garbage block.
  The machine does not assume uniqueness; example (a) shows a write seen through an alias.
- **Garbage**: the spec heap only grows (`run-grows`). A real heap is collected. Relating the two needs the
  shape-independent heap relation of 6.2 restricted to reachable blocks.
- **The label list of `big-small` is the flattening of `ch` with `LTau`s added**: the lemma returns some list
  and does not say which.

---

## 7. Checker obstacles, with exact text

None stopped the work or changed the goal. In order met:

1. **A name of mine shadowed a prelude name.** [RAN] first check of `prim-fn.sl`:
   ``prim-fn.sl:10:4: warning: declaration of `Stop` shadows a previous binder`` with
   `lib/prelude.sl:1347:3: note: shadowed binder is here`. Renamed to `Halt`. Likewise
   ``ex-b.sl:12:7: warning: declaration of `append` shadows a previous binder``; renamed to `append-list`.
2. **Style warning on a two-way match with one long arm.** [RAN], for example,
   ``prim-fn.sl:50:4: warning: lopsided `match`; flatten it with a `let-match` on `AVar` ``. Met 10 times; each
   was rewritten as a `let-match` with the short arms as extra branches (DESIGN.md §52). The final files give no
   warning: [RAN] `grep -c warning run-all.log` printed `0`.
3. **Indentation warnings on `$` chains split over lines.** [RAN] first check of `ex-a.sl`:
   `ex-a.sl:4:3: warning: same indentation (2) as the previous checked line but nesting is 2, expected 1 (matching that line)`.
   Rewritten with a helper `lets` that folds a list of code into nested `CLet`s [READ S2/ex-lib.sl:1-3].
4. **A numeral is opaque in a type.** [QUOTE DESIGN.md:2200-2201 §45] "A numeral is opaque: a `Settled` `Nat` with
   no `is` rule, next to its erased `Numeral` proof." I wrote the answers of `ISame` as `(WImm (Succ (Zero)))` and
   `(WImm (Zero))` in the rules, and used `prove-literal-lt` to get `(Lt 3 7)` for hand-built derivations.
   The checker's own note says so: [RAN] `$B $SPEC neg/same-yes-distinct-bad.sl` printed
   ``note: 5 in `...` is a numeral literal, opaque to the checker by default; `unary`, `prove-literal-lt` or `numeral-of` can expose more``
   (I have cut the quoted term to `...`; the whole note is in `S2/run-all.log`).
5. **No generic result type**, because a type constructor cannot be partly applied (error text in section 3).
   Workaround: one result type per decided relation.
6. **A lemma cannot be passed where a law of the same statement is expected**, because a function's type holds
   its level and its `subterm` marks. [RAN] `$B $SPEC det.sl neg/abs-direct-law-bad.sl` exits 1 with

   ```
   neg/abs-direct-law-bad.sl:37:30: error: argument 3, `lk-fn`, of `select-fn-a`: type mismatch: expected `(Fn laws (erased (Heap) h) (erased (Nat) a) (erased (Block) b1) (erased (Block) b2) (erased (Lookup h a b1) p) (erased (Lookup h a b2) q) -> (erased (Eq (Block) b1 b2) e))`, got `(Fn (level-of lookup-fn) (erased (Heap) h) (erased (Nat) a) (erased (Block) b1) (erased (Block) b2) (subterm erased (Lookup h a b1) p) (erased (Lookup h a b2) q) -> (erased (Eq (Block) b1 b2) e))`
   ```

   Workaround: a one-line wrapper defined at the level the law names [READ S2/abs.sl:29-31].
7. **A value an erased field holds cannot be inspected at the top level**, so I could not feed the choice tree
   that `run` returned for an example into `ren-run`. [INFERENCE from DESIGN.md §28: "erased fields take the
   tokens of §5"]; I did not run an attempt. The worked instance in `corollary.sl` uses a hand-built run instead.

Things I expected to be obstacles and were not: mutual nesting of `Code` through `(List (Code))`; primes in names
(`h'`); absurd branches inside a non-absurd function; an erased call of the non-erased `nat-dec` inside a proof
(`ren-neq` [READ S2/ren.sl:61-65]). No proof file needed a second attempt for a type error; the edits after the
first run of each were for the warnings above.

---

## 8. slc's compile-time store against this abstract heap

I read `self/heap.sl` in full, `self/eval.sl` lines 1 to 260 and 796 to 815, `self/core.sl` lines 2340 to 2430,
`self/elab-main.sl` lines 225 to 290, and `self/base.sl` lines 250 to 320 and 1000 to 1012. Claims below are
about those lines only.

**What the store is.**

- [QUOTE /home/user/sleight/self/heap.sl:1-4] "; self/heap.sl -- the compile-time store: a value is stamped with
  its position in an erased ghost ; history, and refers to other values directly rather than through an address.
  The history makes ; position -> value a function (suffix-unique below), which is what lets the emitter name a
  value ; it has already written."
- [READ /home/user/sleight/self/heap.sl:38-58] `Hist` is the list of every value allocated; a `Value` holds its
  position `pos`, an erased proof that `pos` is the length of the history before it, and its body; a `Ref B l`
  holds a `Value` and an erased proof that the value sits in history `l`.
- [READ /home/user/sleight/self/heap.sl:60-69] `(Store B l)` holds `next`, an erased `(Len B l next)`, and
  `writes`, an `IdMap` from position to a `StoredBody`.
- [QUOTE /home/user/sleight/self/README.md:23-25] "The port retains erased proofs for code contexts, fact-table
  traversals, and heap histories; current mutable contents are stored separately from allocation snapshots."
- [QUOTE /home/user/sleight/self/README.md:110-112] "every value is an address, every step returns the grown
  store with a proof of the growth by which what was held before is widened". The two sources word it
  differently ("is an address" against "refers to other values directly rather than through an address"); in
  the code a reference holds the value and its position both.

**Allocation is a counter.** [READ /home/user/sleight/self/heap.sl:163-170] `alloc` makes the value at position
`next`, returns the store with `(Succ next)` and history `(HAdd _ l v)`, an erased `(Suffix B l2 l)`, and the new
reference. [INFERENCE] In this report's terms that is one admissible choice of `Fresh` address, and `(Len B l next)`
plays the part of `Below`.

**In-place mutation is supported, through an override map.**

- [READ /home/user/sleight/self/heap.sl:204-207] `store-write` sets `writes[position of r]` to the new body and
  returns `(Store B l)` with the **same** history index.
- [READ /home/user/sleight/self/heap.sl:191-202] `store-read` looks the position up in `writes`; on a hit it
  returns the written body, on a miss the body held in the reference's own value, the allocation snapshot.
- [READ /home/user/sleight/self/elab-main.sl:251-268] the interpreter's `CCellWrite` reads the target's block,
  calls `hwrite` with the fields replaced, and returns the same target reference and the same history
  (`(le-refl h2)`). [READ /home/user/sleight/self/core.sl:2421-2422] `hwrite` is `store-write` under a wrapper.
- [QUOTE /home/user/sleight/self/elab-main.sl:270] "; a copy of the block with the writes applied (section 37),
  the old block untouched", and [READ /home/user/sleight/self/elab-main.sl:271-286] `CCellCopy` calls `halloc`.
- Other callers of `hwrite`: [RAN] in `/home/user/sleight`, `grep -n "hwrite\|store-write" self/*.sl` lists, besides
  the two definitions and `self/elab-main.sl:265`, `self/eval.sl:168` (arrays), `self/eval.sl:541`, and
  `self/eval.sl:685`.

**What it proves about itself.**

- Growth: every allocation returns `(Suffix B l2 l)` [READ /home/user/sleight/self/heap.sl:163-165], and every
  holder of references is widened into the later history by a `coerce` whose proof an erased function builds
  (`ref-widen`, `refs-widen`, `stored-map-widen`, and others [READ /home/user/sleight/self/heap.sl:131-158, 211-253]).
- A reference's position is below `next`: `ref-key` returns `(Lt k bound)`
  [READ /home/user/sleight/self/heap.sl:177-182].
- A position names one value: `len-fn`, `suffix-len`, `suffix-unique`, `ref-unique`
  [READ /home/user/sleight/self/heap.sl:74-111], under the comment
  [QUOTE /home/user/sleight/self/heap.sl:71-72] "; ---- a position names one value: the history has one suffix of
  each length, and a value sits at ; the head of the suffix it was allocated onto. Nothing calls these; they are
  the obligation." [RAN] in `/home/user/sleight`, `grep -rn "suffix-unique\|ref-unique\|len-fn\b" self/*.sl | grep -v "^self/heap.sl"`
  printed nothing, which agrees with "Nothing calls these".
- Reading cannot fail: `store-read` has no failing case [READ /home/user/sleight/self/heap.sl:191-202]. In this
  report's terms the `Dangling` stuck state is refuted by the type of a reference.

**What it does not prove.**

- Nothing relates the store after `store-write` to the store before: the result type is `(Store B l)` and no
  proof is returned [READ /home/user/sleight/self/heap.sl:204-205]. `idmap-set` returns a bare `(IdMap V)`
  [READ /home/user/sleight/self/base.sl:308]. [RAN] in `/home/user/sleight`, `grep -n "def-fns.*idmap-\|IdMap :" self/*.sl` lists
  `idmap-get`, `idmap-set`, `idmap-mem`, `idmap-of-list`, `idmap-prefix`, `idmap-pairs`, `idmap-set-bd`, and
  `idmap-widen`; none is a "get after set" law. `idmap-set-bd` is about the map's size
  [READ /home/user/sleight/self/base.sl:1004-1008].
- The erased history records allocation snapshots, not current contents: a write leaves the index `l` as it was.
  So no type in the store speaks of what a block holds now.
- A written body's references are valid in the whole current history
  [READ /home/user/sleight/self/heap.sl:204-207: the body has type `(B (Ref B l))`], so after a write a block may
  point to a block allocated later; an allocation snapshot's references are valid only in the history before it
  [READ /home/user/sleight/self/heap.sl:47]. [UNKNOWN] how the emitter orders or patches such blocks; I did not
  read `self/emit.sl`. `self/README.md:356-357` says each block's addresses are below its own; I did not check
  that sentence against written bodies.

**Word equality in slc and in the reference.** [READ /home/user/sleight/self/eval.sl:804-809] `slot-eq-answer`
answers "some" exactly when the two references have the same position. [READ /home/user/sleight/lib/eval.ml:61]
the reference answers by OCaml's `==`.

**Both answers on equal numbers are observed today.** `S2/probe/slot-eq-nats-compiled.sl` asks `slot-eq` about
one variable against itself, and about `(nat-add 2 3)` against `(nat-add 1 4)`, and prints 1 for "yes" and 0 for
"no". [RAN] in `S2/probe/`:

| Command | Output |
|---|---|
| `/home/user/sleight/_build/default/bin/main.exe slot-eq-nats-compiled.sl` | `(Cons _ 1 $ Cons _ 0 $ Nil _)` |
| `/home/user/sleight/_build/release/slc --interpret slot-eq-nats-compiled.sl` | `(Cons _ 1 $ Cons _ 0 $ Nil _)` |
| `/home/user/sleight/_build/default/bin/main.exe slot-eq-nats-compiled.sl --build ./probe-ref; ./probe-ref` | `(Cons _ 1 $ Cons _ 1 $ Nil _)` |
| `/home/user/sleight/_build/release/slc slot-eq-nats-compiled.sl --build ./probe-slc; ./probe-slc` | `(Cons _ 1 $ Cons _ 1 $ Nil _)` |

Two separately computed 5s answer "no" under both interpreters and "yes" in both compiled programs. [INFERENCE] So a spec that fixed either
answer for equal immediates would contradict one pair of implementations; the two rules `PSameYes` and `PSameNo`
admit all four runs, on the reading that two equal small numbers are one word. This spike's deriving function
answers as the compiled programs do.

**How the two would be related [INFERENCE].** An abstraction relation between `(Store Block l)` and this report's
`Heap`: for each position below `next`, the abstract heap holds, at that position, the image of what
`store-read` returns there. To prove slc's three operations correct against `Alloc`, `Lookup`, and `Update` one
would need (1) get-after-set and get-after-other-set laws for `IdMap`, which are absent; (2) that a position
names one reference, which `ref-unique` gives and nothing uses yet; (3) that position `next` is unused, which
`(Len B l next)` and `ref-key` give. The counter and the positions need no renaming: slc's choices are a legal
resolution of the nondeterministic `Alloc`.

---

## 9. Assessments

All [INFERENCE] unless tagged otherwise; they rest on the measurements above.

### 9.1 Big-step versus small-step for the spec

| | S-big | S-small |
|---|---|---|
| Size beyond the shared rules [RAN, section 3] | 24 lines, 4 rules | 34 lines, 7 rules, plus `Stack` and `Control` |
| Deriving function [READ S2/run-fn.sl, S2/step-fn.sl] | `run` needs fuel | `step` needs none and is total; only the loop `steps` needs fuel |
| A run that has not finished | no derivation exists, so nothing can be said | `(Steps fns h0 c0 ls h c)` says exactly where it is |
| A run that never finishes or gets stuck | indistinguishable: no derivation either way | distinguishable: stuck is a state with no step |
| Choices | a tree index, `Choices`, that mirrors the derivation | a label per step, a list per run |
| Renaming, any second choice | only with the whole renamed tree given up front (`ren-run`) | one step at a time for any fresh address (`sim-alloc`) |
| Reads like DESIGN.md's prose | closer | further: a reader must hold the stack in mind |
| Reasoning about a call as a unit | direct: a sub-derivation | needs a lemma to split a step sequence (the unproved `small-big`) |

I would make **S-small the definition** and keep S-big as a theorem-linked presentation, for three reasons.

1. The previous session's proposal C, which the owner has not ruled on, is an evaluator
   [QUOTE /tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/handoff.md:39] "whose
   single step is a total function, looped by the `Program` driver, with the machine state carrying an erased
   proof tying it to the spec's run".
   With S-small that proof is the `(Step ...)` value `step` already returns, and the loop's invariant is a
   `Steps`. With S-big the loop would need a separate invariant relating a machine state in mid-run to an
   unfinished big-step derivation.
2. The model language has programs that do not finish (4.3), and the two results the previous session gave the
   owner on compile-time termination are about spec runs that may not halt
   [READ /tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/handoff.md:22].
   S-big cannot state anything about such a run.
3. Both are available at once for 58 lines, since `Prim`, `Select`, and the heap relations are shared, and
   `agree.sl`, which holds `big-small`, is 36 lines.

Against: `small-big` is not proved, and S-small's states are less readable. Whether DESIGN.md should describe
the run in either style is the owner's call; §31 says only [QUOTE DESIGN.md:1319-1320 §31] "The semantics is that
of a machine with unlimited stack and heap."

### 9.2 Abstract nondeterministic addresses versus a deterministic counter in the spec itself

- **Cost of nondeterminism, measured.** Three rules (`Fresh`, `Alloc`); the `Below` invariant and three lemmas
  in the deriving function, 30 lines [READ S2/heap-fn.sl:22-51]; one constructor of `Label`. The labels and
  `Choices` are needed anyway for the equality test's two answers.
- **A counter in the spec would not remove `Below`.** With "the new address is `next`" as the rule, a heap whose
  addresses are not all below `next` would let a new block shadow an old one under first-match `Lookup`, and
  `run-keeps` would be false for it. So every theorem would carry `Below` as a hypothesis; the invariant moves
  from the function into the spec's statement of well-formed states.
- **A counter in the spec makes the spec's addresses facts.** Then any evaluator that allocates in another
  order, or allocates blocks the spec does not, cannot match the spec word for word, and each correctness proof must
  carry a renaming. (A session's note about slc, not a decision of the owner's, describes such an allocation:
  [QUOTE /home/user/sleight/ASSUMPTIONS.md:1117-1118] "reading a member allocates its closure block".)
  With `Fresh` in the spec, an evaluator proves only "my address is fresh" and obtains a spec
  derivation with its own addresses, as `prim` does here, and the renaming theorem is proved once, about the
  spec alone.
- **The renaming theorem is the formal content of "an address is an abstract name"**: `ren-run` holds for every
  one-to-one renaming, order-reversing ones included, so no rule can observe order or arithmetic. A spec with a
  counter is not closed under renaming, so it could not have this theorem.
- **DESIGN.md does not choose** (finding 10). Its one sentence with the word is
  [QUOTE DESIGN.md:1700-1702 §36] "A slot may belong to consumed entries; address equality does not change when
  contents do."

I would keep the addresses abstract and nondeterministic in the spec, and the counter in the deriving function
only. The previous session's model B
[QUOTE /tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/handoff.md:36, the four
phrases quoted next] is, as far as this spike goes, implementable as written:
"with no order and no arithmetic" is `Neq` only; "any address never taken before" is `Fresh` on a heap that only
grows (6.3); "a block keeps its address ... whatever is written into it" is `run-keeps`; "find that two words are
the same word, and nothing else" is `ISame` with `same-yes-sound`. The owner has not accepted that model.

### 9.3 A list heap versus an abstract heap interface

- **What the list heap cost, measured.** Of the 71 lemmas in the proof files and the 17 deriving functions,
  22 take the heap's representation apart (they match `Fresh`, `Lookup`, `Update`, `Alloc`, `RenH`, or `Below`
  by constructor): `lookup-fn`, `update-fn`, `alloc-fn`; `lookup-fresh-neq`, `update-fresh-back`, `update-keeps`,
  `alloc-keeps`, `alloc-fresh-back`, `alloc-not-live`, `prim-label-fresh`, `step-alloc-live`; `ren-lookup`,
  `ren-fresh`, `ren-update`, `ren-alloc`, `renh-grow`; and `lookup-dec`, `update`, `below-fresh`, `below-succ`,
  `below-update`, `alloc`. [RAN] `grep -n "HCons\|HNil" det.sl keep.sl agree.sl ren.sl ren-small.sl ren-grow.sl ren-online.sl`
  matches only the definition of `RenH` and lines inside `ren-lookup`, `ren-fresh`, `ren-update`, `ren-alloc`,
  and `renh-grow`; the others reach the list through the constructors of `Lookup`, `Update`, `Fresh`, and
  `Alloc`. Each of the 22 is a 3 to 15-line induction over the list. [INFERENCE] Every other lemma uses the heap
  through these; I classified the 22 by reading, not by a tool.
- **What an abstract interface would look like, tried.** `abs.sl` [READ S2/abs.sl:1-37] restates `Select` over an
  abstract heap type `H` and an abstract lookup relation `Lk`, proves it deterministic from one assumed law
  passed as an erased function, and instantiates it at the list heap. [RAN] `$B $SPEC det.sl abs.sl` exits 0.
  Cost seen: two more erased parameters on the relation and on each of its constructors for one abstract
  relation (a full interface of lookup, update, allocate, and fresh would add about five); one function-typed
  hypothesis per law on every lemma that uses it; and a wrapper per law at the instantiation (obstacle 6).
- **The trade.** With an interface the 16 lemma statements among the 22 become assumptions of the spec. A
  missing or wrong law would make the spec unsound or too weak, and nobody would be told. With the list heap
  there is nothing to assume: the laws are theorems, and a faster heap (slc's trie, a real machine's memory) is
  related to the list by a refinement proof on its side.

I would put the concrete list heap in the spec and treat the laws as lemmas about it. The list is slow only as
an evaluator; the spec is not one.

### 9.4 What closures would add

[INFERENCE] None of this was built.

- **A kind of word or block for a function value.** DESIGN.md says
  [QUOTE DESIGN.md:1247-1248 §29] "a function's value is its compiled code" and
  [QUOTE DESIGN.md:1327 §32] "A function defined by `def-fns` is a closure over its scope." The handoff records
  as not worked out "which kind of word a function value is" (handoff.md:36). Either a closure is a block
  (code index plus captured words), allocated like any other, or a new word kind.
- **A call through a word**: `CCall` would take an atom; the rule would look the closure up and run its code in
  the captured words followed by the arguments. One more stuck state: calling a word that is not a function.
- **Identity of function words**: [QUOTE DESIGN.md:1488-1489 §33] "The pointer of a `delegate`-bodied function is
  its callee's pointer (§19)." and `fn-same` (§70) both need two function words to be comparable as words.
- **Recursion among closures**: a `def-fns` block's functions refer to each other, so either closure blocks are
  cyclic or calls go through a table as here.
- **`def-unique`**: a function that captures `unique` values and is called once (§32); the machine need not know,
  as it does not know about `unique` anywhere else.
- **Renaming**: if closures are ordinary blocks, `RenB` already covers them; if they are a new word kind,
  one more case in `RenW` and in each of the 7 "grows" lemmas.

---

## 10. What is missing relative to DESIGN.md's memory model

Listed, not modelled. Each item quotes the text the model does not meet.

1. **Tags only where needed.** [QUOTE DESIGN.md:1465-1468 §33] "A value carries a tag only when its type is an
   enum with more than one non-phantom constructor. A block's tag counts only the constructors with fields. A
   phantom constructor takes no discriminant." Every block here has a tag.
2. **Bare single fields and newtypes.** [QUOTE DESIGN.md:1464-1465 §33] "A value is the tuple of its
   constructor's non-erased fields; a single field is stored bare." and [QUOTE DESIGN.md:1478-1483 §33] "A
   newtype value built by a wrapping constructor is represented exactly as that constructor's one non-erased
   field, with no tag and no wrapper. That representation is mandatory for a type marked `newtype` and forbidden
   for a type that is not marked: an unmarked type of newtype shape is a block (§37)." Here every constructor
   application allocates. I do not know how the first sentence's "a single field is stored bare" and the last
   sentence's "an unmarked type of newtype shape is a block" fit together; I quote both and interpret neither.
3. **Hollow values, tag slots, and the unspecified word.** [QUOTE DESIGN.md:1468-1476 §33] "A type is **hollow**
   when it is not marked `extern`, carries no tag, and none of its non-phantom constructors has a non-erased
   field. A value with no non-erased field is the word of the `Nat` of its position among the fieldless
   non-phantom constructors when its type is tagged, the word of `vacant-slot` (§35) when its type is untagged
   and not marked `extern`, however the value was built, and an unspecified word otherwise. In the first two
   cases this is the word of its constructor's tag slot (§35)." The model has immediates by position only; it
   has no "unspecified word" and no tag slots.
4. **`vacant-slot`.** [QUOTE DESIGN.md:1588-1589 §35] "Its runtime word is what `cell-alloc` puts in a vacant
   slot, and the word of every value of a hollow type (§33)." and [QUOTE DESIGN.md:1476-1477 §33] "`vacant-slot`'s
   word is that of `Nat` 0." The examples write `(AImm 0)` by hand where a vacant slot is meant.
5. **Function values.** Section 9.4.
6. **Extern types.** [QUOTE DESIGN.md:1942-1944 §42] "For a type, its constructors and `Matchable` say what its
   values are and how they are taken apart, and the FFI supplies the representation together with construction
   and matching over it." and [QUOTE DESIGN.md:2004 §43] "A `unique` value of an extern type may be mutated in
   place by the FFI." Not modelled. The handoff records as open whether the spec runs the models or the FFI.
7. **What an immediate is.** The model's `(WImm n)` holds any `Nat`. The prelude's `Nat` is itself an extern
   type [QUOTE /home/user/sleight/lib/prelude.sl:10-11] "(def-adts $ (Nat : -> Type) enum extern";
   [QUOTE DESIGN.md:2236-2237 §45] "**Left to the implementation.** How a `Nat`, `Char` or `String` is held at
   runtime"; and [QUOTE DESIGN.md:2062-2063 §44] "`ImmNat` gives it for a `Nat` below `u62-modulus`". [INFERENCE] So
   a large `Nat` need not be an immediate, and the model's "yes" for two equal large numbers is a choice a real
   machine may not make.
8. **Stores marked as between immediates.** [QUOTE DESIGN.md:1791-1792 §37] "`(imm o n)` before an argument, or
   before a `cell-write` item, marks a store whose old and new words are both immediates." One kind of store
   here.
9. **Several results, and results that are not passed.** [QUOTE DESIGN.md:1074 §26] "A function returns zero or
   more values." and [QUOTE DESIGN.md:1659-1660 §36] "An `at` return is absent from the physical values of a
   call." One word per result here; at-functions and at-matches (§39, §40), which compile to nothing, are absent.
10. **Slots as values, and `cell-match`.** [QUOTE DESIGN.md:1802-1803 §38] "At runtime, the value of a slot is a
    word, either a pointer or an immediate." The model has no instruction that reads a word out without a match.
11. **Constants that are addresses.** [QUOTE DESIGN.md:1300-1301 §29] "The resulting values come back to be
    stored (§5) and embedded as constants." The model's code holds immediates only, so code is unchanged by a
    renaming; with embedded addresses it would not be.
12. **Crashes.** [QUOTE DESIGN.md:1320-1321 §31] "A real run may crash where the host cannot represent what is
    asked of it. A crash produces no value, never a different one." The relations have no crash outcome.
    [INFERENCE] That matches the sentence if a crash is read as "the implementation gives no derivation".
13. **The world.** `World`, `Program`, requests, and `world-do` (§42) are absent.
14. **Arrays and the other extern-modelled structures** (§44, §69) are absent.
15. **Order of evaluation inside one form** is not chosen by the model (section 1, first bullet).

---

## Things I am least sure of

1. **That the atoms-only syntax is a fair stand-in.** It rests on one sentence of §15 and sidesteps the open
   question of evaluation order instead of answering it.
2. **That the `Choices` index belongs in the spec's `Run`.** It is there to make determinism statable. A reader
   may prefer `Run` without it and a second, instrumented relation; I did not build that alternative, so I cannot
   compare the cost.
3. **That the same-shape heap relation is the right one for obligation (b).** It serves "two runs of one
   program". The brief also names "a compile-time heap to the run-time heap of the emitted program"; my claim
   that only five lemmas would change for a shape-independent relation is an estimate from a grep, not a proof.
4. **`small-big` is unproved.** The recommendation in 9.1 leans on the two styles agreeing in both directions.
5. **The `Dangling` stuck state is unreachable from an empty start**: reasoned, not proved.
6. **No typed formulation was tried.** Everything in 4.3's last column and in 6.5 is inference.
7. **My reading of slc.** I read `self/heap.sl` whole and parts of four other files. I did not read
   `self/emit.sl`, so I do not know how written bodies with forward references are emitted, and I did not run
   slc's store in isolation.
8. **"Proved" means "both implementations accept the erased function".** If the checker has a soundness bug in
   erased matching or refutation, a lemma here could be wrong. The seven refusals in `S2/neg/` show the checker
   rejects the wrong variants I thought of, not all wrong variants.
9. **The immediates.** Treating every `Nat` as an immediate, and answering "yes" for equal immediates, is
   simpler than what §44 and §45 allow, and it is not what the two interpreters do today (the probe in
   section 8).
10. **Line counts depend on my formatting.** Lines run up to 168 characters; the byte counts are the more
    honest measure.
