# S4: reading source text as a specification relation in Sleight (prototype)

One Claude session's spike. Nothing below is the owner's decision. Code:
`/tmp/claude-0/-home-user-sleight/2d67e34a-6457-5edb-89e1-4a78ef649af6/scratchpad/proto/S4/` (see its `RUN.md`).

Conventions for this report. `M` is `/home/user/sleight/_build/default/bin/main.exe`, `S` is
`/home/user/sleight/_build/release/slc`, and every command is run from the S4 directory. "Tokens" in the
size tables are parentheses and whitespace-separated words, counted by `tools/summary.py`. Claim tags are
as the common brief defines them.

**The prototype is a SUBSET.** It reads `(`, `)`, the bare `$` token, atoms, and `;` comments. It has no
string literals, character literals, numerals, raw names, `_`, `__` rule, pragmas, or positions. A `;!`
line is read as a comment, and `42` as an atom. Section 13 lists what each omission would add.

## 1. Findings that bear on decisions

1. **Reading can be specified as two small inductive relations, and the "accepted or rejected" theorem
   for it is cheap.** `Lex text toks` (text to tokens) and `Items toks forms end` (tokens to forms), a
   positive failure relation, a total reader `read : text -> (Read text)` with two outcomes, and the
   lemmas "never both", "one reading", and "one mistake" all pass `--goal proved` under both
   implementations.
   [RAN] `$M syntax.sl spec.sl read.sl proof.sl qed.sl --goal proved` prints
   ``spec.sl:13:1: note: proved `(goal many (Reader))` ``, ``qed.sl:1:1: note: by this `qed` ``, and
   `--goal proved: PASS`, exit 0, in 0.58 s; the same command with `$S` prints the same three lines,
   exit 0, in 0.39 s.
2. **Cost.** Relations 112 lines (2301 tokens); deriving function 95 lines (2021 tokens, of which 20
   lines are three termination lemmas); lemmas 180 lines (3240 tokens). The lemmas are 0.75 times the
   size of relations plus function in tokens (0.87 in lines), or 1.4 times the relations alone.
   [RAN] `python3 tools/summary.py`, output in section 9. No checker obstacle blocked the work;
   section 11 lists every one. [RAN] The first complete version (kept in
   `variants/flat-lex/`) passes with `(cd variants/flat-lex && $M spec.sl read.sl proof.sl qed.sl --goal proved)`.
3. **The two implementations disagree about what whitespace is, and DESIGN.md does not say.**
   [RAN] `diff/probe.sh '(show-args a\fb)'` prints `main.exe  : "a\x0cb"` (one atom) and
   `slc       : "a b"` (two atoms). The same split happens for bytes `0x0b`, `0x00`, and `0x1f`.
   Details in Q1 of section 12. This needs an owner decision before a reading relation can be called
   the specification.
4. **Formulation.** I recommend (A), a tokenizing relation plus an items relation in recursive-descent
   style, as the working definition, with (B), printing, proved equivalent and available as the
   statement a human reads. At the token level the two are the same rules read in opposite directions;
   the equivalence is two inductions of 13 and 12 lines. (B) alone gives neither a failure relation nor a reader.
   [RAN] `$M syntax.sl read.sl adequacy-spec.sl adequacy-proof.sl --goal proved` and the same with `$S`
   both print `--goal proved: PASS`. Section 10.
5. **The three lemmas do not show the relation is the right one.** [INFERENCE] They would hold for a
   degenerate relation, for example one under which every text is `Unreadable` with one fixed
   mistake; this follows from their statements. They also hold unchanged for any delimiter table.
   [RAN] `mutations/run.sh`, case M5: with form feed and vertical tab added to the table in a copy of
   `syntax.sl`, the unchanged `spec.sl`, `read.sl`, `proof.sl`, and `qed.sl` still print
   `--goal proved: PASS`, and `(a\fb)` then reads as `(a b)` where the unchanged table gives one atom.
   Evidence that the relation says what the implementations do comes from elsewhere: a
   round-trip theorem (section 10), 22 hand cases, and a corpus comparison in which 1132 of 1137
   repository files without literals or pragmas read identically in the prototype, the reference, and
   slc, the other 5 being the `__` rule that the subset omits (section 7).
6. **A goal's `Fn` type exposes the proof's induction.** A `subterm` mark is part of a function type,
   so a recursive lemma cannot be passed where the goal names an unmarked `Fn`. The workaround is a
   non-recursive wrapper. Section 11, obstacle 1.
7. **The deriving function as written needs stack proportional to the token count.**
   [RAN] Compiled with `$S syntax.sl read.sl show.sl cli.sl --build`, it read a 240 KB synthetic text
   (120000 tokens) and failed on a 360 KB one (180000 tokens) with
   `Fatal error: exception Stack overflow`, under `ulimit -s` of 8192. A constant-stack reader that
   still returns derivations is extra proof work not done here. Section 5.
8. **Within one file, both implementations read the whole text before elaborating any form; across
   files they read one file at a time.** DESIGN.md is silent on this. Q15 of section 12.

## 2. Context

- [QUOTE handoff.md:21] "It should be a theorem that every program's source code is either accepted or rejected as an error."
- [QUOTE mini/README.md:161] "A reader from text to `Sexp` is not written; tests build `Sexp` by hand."
- [READ self/reader.sl:245-333, 372-419] slc's own reader is already fuel-free: the tokenizer functions
  each recurse on a `(subterm many (String) s)` parameter, continuing after a string literal through
  `(subterm st)` with `st` from `suffix-sub` (lines 236-240, 328-333), and `parse-toks` is a fold over
  the token list with a stack of open frames. It returns no derivation of any relation.

## 3. The specification

**Text representation.** The text is the prelude's `String` and its characters are `Char`. Why:
[QUOTE DESIGN.md:1170-1172 §27] "`(Fn L (many (String) x) -> (many (String) y))`, with the prelude's
`String`, is applied to all of standard input, and its result is written to standard output", so a
theorem about `String` is about what a Sleight program is handed. It cost three pragma lines, because
[QUOTE lib/prelude.sl:1112] ";! warn SCons copies the whole string, O(n); build a `Rope` and `flatten` it once"
warns at each non-erased `SCons`. A `(List (Nat))` of byte codes was not tried.
[INFERENCE] It would need the same table design, since §45 makes numerals opaque as well; checkable by
porting `Class` to `nat-eq`.

**The relations**, the whole of `syntax.sl`:

```scheme
(def-adts $ (Delim : -> Type)
  enum
  (many DSpace : -> (Delim))
  (many DOpen : -> (Delim))
  (many DClose : -> (Delim))
  (many DSemi : -> (Delim)))

(def-adts $ (Kind : -> Type)
  enum
  (many KWord : -> (Kind))
  (many KDelim : (many (Delim) d) -> (Kind)))

(def-adts $ (Entry : -> Type)
  enum
  (many MkEntry : (many (Char) c) (many (Delim) d) -> (Entry)))

(let ((many delims))
  (Cons _ (MkEntry #\space (DSpace)) $ Cons _ (MkEntry #\newline (DSpace)) $ Cons _ (MkEntry #\tab (DSpace)) $ Cons _ (MkEntry #\x0d (DSpace))
    $ Cons _ (MkEntry #\x28 (DOpen)) $ Cons _ (MkEntry #\x29 (DClose)) $ Cons _ (MkEntry #\x3b (DSemi)) $ Nil _))

(def-adts $ (Class : ((List (Entry)) table) ((Char) c) ((Kind) k) -> Type)
  enum
  (many ClassWord : (erased (Char) c) -> (Class (Nil (Entry)) c (KWord)))
  (many ClassHere : (erased (Char) c) (erased (Delim) d) (erased (List (Entry)) rest) -> (Class (Cons (Entry) (MkEntry c d) rest) c (KDelim d)))
  (many ClassThere : (erased (Char) c e) (erased (Delim) d) (erased (Kind) k) (erased (List (Entry)) rest)
     (erased (Apart (Char) CharLt c e) a) (erased (Class rest c k) p) -> (Class (Cons (Entry) (MkEntry e d) rest) c k)))

(def-adts $ (Tok : -> Type)
  enum
  (many TOpen : -> (Tok))
  (many TClose : -> (Tok))
  (many TDollar : -> (Tok))
  (many TAtom : (many (String) name) -> (Tok)))

(def-adts $ (Comment : ((String) text) ((String) after) -> Type)
  enum
  (many CommentEnd : -> (Comment (SNil) (SNil)))
  (many CommentLine : (erased (String) rest) -> (Comment (SCons #\newline rest) rest))
  (many CommentSkip : (erased (Char) c) (erased (String) rest after) (erased (Apart (Char) CharLt c #\newline) a) (erased (Comment rest after) p)
     -> (Comment (SCons c rest) after)))

(def-adts $ (Word : ((String) text) ((String) w) ((String) after) -> Type)
  enum
  (many WordEnd : -> (Word (SNil) (SNil) (SNil)))
  (many WordStop : (erased (Char) c) (erased (Delim) d) (erased (String) rest) (erased (Class delims c (KDelim d)) k)
     -> (Word (SCons c rest) (SNil) (SCons c rest)))
  (many WordMore : (erased (Char) c) (erased (String) rest w after) (erased (Class delims c (KWord)) k) (erased (Word rest w after) p)
     -> (Word (SCons c rest) (SCons c w) after)))

;! suppress warn SCons
(let ((many dollar)) (SCons #\$ (SNil)))
;! restore warn SCons

(def-adts $ (TokOf : ((String) w) ((Tok) t) -> Type)
  enum
  (many TokDollar : -> (TokOf dollar (TDollar)))
  (many TokAtom : (erased (String) w) (erased (Apart (String) StrLt w dollar) a) -> (TokOf w (TAtom w))))

(def-adts
  ((Lex : ((String) text) ((List (Tok)) toks) -> Type)
    enum
    (many LexEnd : -> (Lex (SNil) (Nil (Tok))))
    (many LexChar : (erased (Char) c) (erased (Kind) k) (erased (String) rest) (erased (List (Tok)) toks)
       (erased (Class delims c k) ck) (erased (LexAfter k c rest toks) p) -> (Lex (SCons c rest) toks)))
  ((LexAfter : ((Kind) k) ((Char) c) ((String) rest) ((List (Tok)) toks) -> Type)
    enum
    (many AfterSpace : (erased (Char) c) (erased (String) rest) (erased (List (Tok)) toks) (erased (Lex rest toks) p)
       -> (LexAfter (KDelim (DSpace)) c rest toks))
    (many AfterOpen : (erased (Char) c) (erased (String) rest) (erased (List (Tok)) toks) (erased (Lex rest toks) p)
       -> (LexAfter (KDelim (DOpen)) c rest (Cons (Tok) (TOpen) toks)))
    (many AfterClose : (erased (Char) c) (erased (String) rest) (erased (List (Tok)) toks) (erased (Lex rest toks) p)
       -> (LexAfter (KDelim (DClose)) c rest (Cons (Tok) (TClose) toks)))
    (many AfterSemi : (erased (Char) c) (erased (String) rest after) (erased (List (Tok)) toks) (erased (Comment rest after) q) (erased (Lex after toks) p)
       -> (LexAfter (KDelim (DSemi)) c rest toks))
    (many AfterWord : (erased (Char) c) (erased (String) rest w after) (erased (Tok) t) (erased (List (Tok)) toks)
       (erased (Word rest w after) q) (erased (TokOf (SCons c w) t) o) (erased (Lex after toks) p)
       -> (LexAfter (KWord) c rest (Cons (Tok) t toks)))))

(def-adts $ (Form : -> Type)
  enum
  (many FAtom : (many (String) name) -> (Form))
  (many FList : (many (List (Form)) items) -> (Form)))

(def-adts $ (Ending : -> Type)
  enum
  (many AtEnd : -> (Ending))
  (many AtClose : (many (List (Tok)) after) -> (Ending)))

(def-adts $ (Items : ((List (Tok)) toks) ((List (Form)) forms) ((Ending) end) -> Type)
  enum
  (many ItemsEnd : -> (Items (Nil (Tok)) (Nil (Form)) (AtEnd)))
  (many ItemsClose : (erased (List (Tok)) after) -> (Items (Cons (Tok) (TClose) after) (Nil (Form)) (AtClose after)))
  (many ItemsAtom : (erased (String) a) (erased (List (Tok)) ts) (erased (List (Form)) fs) (erased (Ending) end) (erased (Items ts fs end) p)
     -> (Items (Cons (Tok) (TAtom a) ts) (Cons (Form) (FAtom a) fs) end))
  (many ItemsOpen : (erased (List (Tok)) ts after) (erased (List (Form)) inner fs) (erased (Ending) end)
     (erased (Items ts inner (AtClose after)) p) (erased (Items after fs end) q)
     -> (Items (Cons (Tok) (TOpen) ts) (Cons (Form) (FList inner) fs) end))
  (many ItemsDollar : (erased (List (Tok)) ts after) (erased (List (Form)) inner) (erased (Items ts inner (AtClose after)) p)
     -> (Items (Cons (Tok) (TDollar) ts) (Cons (Form) (FList inner) (Nil (Form))) (AtClose after))))

(def-adts $ (Reads : ((String) text) ((List (Form)) forms) -> Type)
  enum
  (many ReadsBy : (erased (String) text) (erased (List (Tok)) toks) (erased (List (Form)) forms)
     (erased (Lex text toks) l) (erased (Items toks forms (AtEnd)) p) -> (Reads text forms)))

(def-adts $ (Mistake : -> Type)
  enum
  (many MissingClose : -> (Mistake))
  (many MissingCloseAfterDollar : -> (Mistake))
  (many UnexpectedClose : -> (Mistake)))

(def-adts $ (ItemsFail : ((List (Tok)) toks) ((Mistake) m) -> Type)
  enum
  (many FailAtom : (erased (String) a) (erased (List (Tok)) ts) (erased (Mistake) m) (erased (ItemsFail ts m) p) -> (ItemsFail (Cons (Tok) (TAtom a) ts) m))
  (many FailOpenInside : (erased (List (Tok)) ts) (erased (Mistake) m) (erased (ItemsFail ts m) p) -> (ItemsFail (Cons (Tok) (TOpen) ts) m))
  (many FailOpenEnd : (erased (List (Tok)) ts) (erased (List (Form)) inner) (erased (Items ts inner (AtEnd)) p)
     -> (ItemsFail (Cons (Tok) (TOpen) ts) (MissingClose)))
  (many FailOpenAfter : (erased (List (Tok)) ts after) (erased (List (Form)) inner) (erased (Mistake) m)
     (erased (Items ts inner (AtClose after)) p) (erased (ItemsFail after m) q) -> (ItemsFail (Cons (Tok) (TOpen) ts) m))
  (many FailDollarInside : (erased (List (Tok)) ts) (erased (Mistake) m) (erased (ItemsFail ts m) p) -> (ItemsFail (Cons (Tok) (TDollar) ts) m))
  (many FailDollarEnd : (erased (List (Tok)) ts) (erased (List (Form)) inner) (erased (Items ts inner (AtEnd)) p)
     -> (ItemsFail (Cons (Tok) (TDollar) ts) (MissingCloseAfterDollar))))

(def-adts $ (Unreadable : ((String) text) ((Mistake) m) -> Type)
  enum
  (many UnreadableItems : (erased (String) text) (erased (List (Tok)) toks) (erased (Mistake) m)
     (erased (Lex text toks) l) (erased (ItemsFail toks m) p) -> (Unreadable text m))
  (many UnreadableClose : (erased (String) text) (erased (List (Tok)) toks after) (erased (List (Form)) forms)
     (erased (Lex text toks) l) (erased (Items toks forms (AtClose after)) p) -> (Unreadable text (UnexpectedClose))))

(def-adts $ (Read : ((String) text) -> Type)
  enum
  (many Accepted : (erased (String) text) (many (List (Form)) forms) (erased (Reads text forms) p) -> (Read text))
  (many Rejected : (erased (String) text) (many (Mistake) m) (erased (Unreadable text m) p) -> (Read text)))
```

**How each rule answers to DESIGN.md.** These mappings are my reading; the owner has not seen them.

- `delims` and `Class`. [QUOTE DESIGN.md:41-42 §1] "An atom is any run of characters other than
  whitespace, parentheses and `;`." The table lists exactly those; `Class table c k` looks `c` up,
  first entry first, and answers `(KWord)` when no entry matches. Whitespace is space, newline, tab,
  and carriage return, which is the reference's set (Q1). A character literal's code is opaque to the
  checker ([QUOTE DESIGN.md:2212-2213 §45] "A character literal is transparent down to its opaque
  `Nat`"), so `ClassThere` carries `Apart` evidence from `char-eq` and no rule compares two literals.
- `Word`. A word is a maximal run: it stops only at the end of the text or before a delimiter.
- `Comment`. [QUOTE DESIGN.md:40-41 §1] "A `;` starts a comment that runs to the end of the line."
  The line ends at `#\newline` or at the end of the text.
- `TokOf`. [QUOTE DESIGN.md:70 §2] "Only a bare `$` token is special; `foo$bar` is an ordinary atom."
  The word that is exactly `$` is `TDollar`; any word apart from it, in the prelude's string order, is
  an atom.
- `Lex` and `LexAfter`. The first character's kind decides: whitespace is skipped, a parenthesis is a
  token, `;` skips a comment, and a word character starts a word.
- `Items toks forms end` reads items until the terminator and says where it stopped: `(AtEnd)` at the
  end of the tokens, or `(AtClose after)` before a `)` that `after` follows.
  [QUOTE DESIGN.md:66-69 §2] "`$` opens a list form exactly as `(` does, but it does not consume the
  `)` that ends it. The form reads items until the terminator of the enclosing form, and leaves that
  terminator for the enclosing form to consume. If there is no enclosing form, the missing `)` is an error."
  `ItemsOpen` reads the inner items to `(AtClose after)` and goes on with `after`, which consumes the
  `)`. `ItemsDollar` reads the inner items to `(AtClose after)` and hands the same `(AtClose after)`
  up, so the `)` is left, and the `$` form is the last item of its enclosing form. Neither rule
  applies when the inner items stop at `(AtEnd)`; that is the missing `)`.
- `Reads text forms`: the text has tokens whose items run to `(AtEnd)`.

Example. The tokens `( a $ b )` read to `(a (b))`: `ItemsOpen` over
`Items [a $ b )] [a (b)] (AtClose [])` and `ItemsEnd`; the first by `ItemsAtom` over
`Items [$ b )] [(b)] (AtClose [])`, which is `ItemsDollar` over `Items [b )] [b] (AtClose [])`.
[RAN] `printf '(a $ b)' | $M syntax.sl read.sl show.sl cli.sl` prints `(a (b))`.

**Design choices inside (A)**, each a session's choice.

- `Ending` instead of "the remaining tokens". With the remaining tokens as the third index, the
  function had to learn that they are empty or start with `)`, which needs a shape lemma and absurd
  branches. [INFERENCE] I did not build that version; the claim rests on the type of `ItemsOpen`'s
  first premise.
- Table-driven `Class` instead of one rule per character. [INFERENCE] One rule per delimiter character
  needs each pair of distinct literals refuted, by `prove-literal-lt` as `tests/prove_literal_lt_char.sl`
  does, or by `unary`; the table needs only that `Apart c c` is absurd. Not built the other way.
- `Lex` indexed by the first character's kind (`LexAfter`) instead of six flat rules. Both were built.
  [RAN] `python3 tools/count.py variants/flat-lex/spec.sl variants/flat-lex/proof.sl` gives the flat
  `Lex` 14 lines and 423 tokens with `lex-fn` 47 lines and 825 tokens; `python3 tools/count.py syntax.sl proof.sl`
  gives the indexed `Lex` 19 lines and 467 tokens with `lex-fn` 33 lines and 507 tokens. The flat proof
  needs an absurd branch for every pair of different rules; the index refutes them unwritten.
- Recursive descent, not a stack machine, for the relation. [INFERENCE] A stack of open frames, as
  `self/reader.sl` has, is a way to compute; as a specification the owner would have to check an
  invariant instead of a grammar.

## 4. The failure relation

`ItemsFail toks m` has one rule for each way the items of `toks` have no derivation:
a mistake further on (`FailAtom`, `FailOpenInside`, `FailDollarInside`, `FailOpenAfter`), a `(` whose
items run to the end (`FailOpenEnd`), and a `$` whose items run to the end (`FailDollarEnd`).
`Unreadable text m` adds the top level: the items stop before a `)` that nothing opened
(`UnreadableClose`). In this subset every text has tokens, so every mistake is an items mistake.
[RAN] The 22 cases of `tests.sl` include nine rejected texts, three per mistake; output in section 7.

The mistake reported for a text with several is fixed by the relation, and agrees with both
implementations on the nine texts of `diff/run.sh`.
[RAN] For `(a)) (b` all three print ``unexpected `)` ``, and for `(a $ (b` all three print
``missing `)` `` (section 7).

## 5. The deriving function

`read.sl`. Signatures:

```scheme
classify : (subterm many (List (Entry)) table) (many (Char) c) -> (many (Kind) k) (erased (Class table c k) p)
comment  : (subterm many (String) text) -> (many (String) after) (erased (Comment text after) p)
word     : (subterm many (String) text) -> (many (String) w) (many (String) after) (erased (Word text w after) p)
tok-of   : (many (String) w) -> (many (Tok) t) (erased (TokOf w t) p)
lex      : (subterm many (String) text) -> (many (List (Tok)) toks) (erased (Lex text toks) p)
items    : (subterm many (List (Tok)) toks) -> (many (Parsed toks) r)
read     : (many (String) text) -> (many (Read text) r)
```

`Parsed toks` is `ParsedOk` with forms, an `Ending`, and an erased `Items` derivation, or `ParsedBad`
with a `Mistake` and an erased `ItemsFail` derivation.

- **Two outcomes.** `Read` has the constructors `Accepted` and `Rejected` and no other.
  [RAN] `grep -n "fuel\|Stuck\|stuck" *.sl` in the S4 directory prints nothing.
- **Termination is structural, with no fuel.** Every recursive call is on the tail of the text or
  token list, except three that continue after a segment: `lex` after a word, `lex` after a comment,
  and `items` after a nested list. Those carry `(subterm s)` with `s` a `Subterm` proof from one of
  three erased lemmas, each an induction on a derivation that uses only `prove-subterm` and
  `subterm-trans`:

  ```scheme
  comment-sub : (erased (Char) x) (erased (String) text after) (subterm erased (Comment text after) p) ->
      (erased (Subterm (String) after (String) (SCons x text)) s)
  word-sub : (erased (Char) x) (erased (String) text w after) (subterm erased (Word text w after) p) ->
      (erased (Subterm (String) after (String) (SCons x text)) s)
  items-sub : (erased (List (Tok)) toks after) (erased (List (Form)) forms) (subterm erased (Items toks forms (AtClose after)) p) ->
      (erased (Subterm (List (Tok)) after (List (Tok)) toks) s)
  ```

  [READ read.sl:1-106] whole file. This is the idiom [READ self/reader.sl:236-240, 328-333] slc's
  tokenizer uses after a string literal.
- **It runs compiled.** [RAN] `$S syntax.sl read.sl show.sl cli.sl --build ./reader && printf '(a $ b ; c\n $ d) e' | ./reader`
  prints `(a (b (d))) e`.
- **Stack.** `word`, `items`, and the token-producing branches of `lex` cons after their recursive
  call, so those calls are marked `notail`. [READ read.sl:23-28, 42-65, 80-99]
  [RAN] A Python loop over the compiled `./reader` with the text `(` + n/6 copies of `(f x $ g y)` + `)`:
  n = 60000 (120 KB) exit 0 in 0.04 s; n = 120000 (240 KB) exit 0; n = 180000 (360 KB) exit 2 with
  `Fatal error: exception Stack overflow`. `ulimit -s` printed 8192. Interpreted by `$M`, n = 60000
  took 4.30 s. [RAN] The same 360 KB text wrapped as `(show-args ...)` and run through
  `$M --no-shape-note diff/showargs.sl big.sl` and `$S --interpret --no-shape-note diff/showargs.sl big.sl`
  exits 0 under both (2.0 s and 1.2 s), so both real readers handle the size at which the prototype
  overflows. At 1.2 MB (600000 tokens) `$M` exits 0 and `$S` exits 2 with
  `Fatal error: exception Stack overflow`. [UNKNOWN] Whether that slc overflow is in its reader or
  in the recursion of my `show-args` macro. [QUOTE DESIGN.md:1320-1321 §31] "A real run may crash where the host cannot represent
  what is asked of it. A crash produces no value, never a different one."
  [INFERENCE] A constant-stack reader that returns derivations needs accumulators and a lemma tying
  the reversed accumulator to the relation; that work is not in the cost figures. Checkable by writing it.

## 6. The lemmas and the goal

`spec.sl`, whole:

```scheme
(def-adts $ (Reader : -> Type)
  enum
  (many MkReader : (erased (Level) L N D M)
     (many (Fn L (many (String) text) -> (many (Read text) r)) read)
     (erased (Fn N (erased (String) text) (erased (List (Form)) forms) (erased (Mistake) m)
                   (erased (Reads text forms) p) (erased (Unreadable text m) q) -> (erased (False) f)) never-both)
     (erased (Fn D (erased (String) text) (erased (List (Form)) f1 f2)
                   (erased (Reads text f1) p) (erased (Reads text f2) q) -> (erased (Eq (List (Form)) f1 f2) e)) one-reading)
     (erased (Fn M (erased (String) text) (erased (Mistake) m1 m2)
                   (erased (Unreadable text m1) p) (erased (Unreadable text m2) q) -> (erased (Eq (Mistake) m1 m2) e)) one-mistake)
     -> (Reader)))

(goal many (Reader))
```

`qed.sl`:
`(qed (MkReader (level-of read) (level-of never-both) (level-of one-reading) (level-of one-mistake) read never-both one-reading one-mistake))`.
The shape follows [QUOTE DESIGN.md:3134 §71] "A goal is one type, not a telescope; an existential,
such as a function with its level, is packaged by an ADT (§21)." and the verdict spike.

All three theorems are proved, not only stated. The proof structure, all erased functions by
induction on the first derivation (`proof.sl`):

| lemma | says | lines |
|---|---|---|
| `char-apart-irrefl`, `str-apart-irrefl` (+2) | no character or string is apart from itself | 15 |
| `class-fn` | a character has one kind under a table | 8 |
| `comment-fn`, `word-fn`, `tok-fn` | each segment relation is a function of the text | 24 |
| `lex-fn` with `after-fn` | a text has one token list | 33 |
| `items-fn` | tokens have one list of items and one ending | 23 |
| `items-excl` | no tokens have both `Items` and `ItemsFail` | 20 |
| `fail-fn` | tokens have one mistake | 27 |
| `never-both`, `one-reading`, `one-mistake` | the goal's three | 30 |

[RAN] The four runs, with their full output:

```
$ $M syntax.sl spec.sl read.sl proof.sl qed.sl --goal proved
spec.sl:13:1: note: proved `(goal many (Reader))`
qed.sl:1:1: note: by this `qed`
--goal proved: PASS
$ $S syntax.sl spec.sl read.sl proof.sl qed.sl --goal proved
spec.sl:13:1: note: proved `(goal many (Reader))`
qed.sl:1:1: note: by this `qed`
--goal proved: PASS
$ $M syntax.sl read.sl adequacy-spec.sl adequacy-proof.sl --goal proved
adequacy-spec.sl:42:1: note: proved `(goal erased (Adequate))`
adequacy-proof.sl:85:1: note: by this `qed`
--goal proved: PASS
$ $S syntax.sl read.sl adequacy-spec.sl adequacy-proof.sl --goal proved
adequacy-spec.sl:42:1: note: proved `(goal erased (Adequate))`
adequacy-proof.sl:85:1: note: by this `qed`
--goal proved: PASS
```

[RAN] `$M --warnings-as-errors --warn-unused syntax.sl spec.sl read.sl proof.sl qed.sl --goal proved`
and `$M --no-extern syntax.sl spec.sl read.sl proof.sl qed.sl --goal proved` also end in
`--goal proved: PASS`.

The `Reader` goal rests on no compile-time evaluation.
[RAN] `grep -n "comptime-match" *.sl` lists only seven lines of `adequacy-proof.sl` and one of `tests.sl`.

## 7. Tests and comparisons with the implementations

**Twenty-two cases.** `tests.sl` holds text and expected result; a `comptime-match` on the conjunction
makes a wrong result an elaboration error.
[RAN] `$M syntax.sl read.sl show.sl tests.sl < /dev/null` (a newline inside a text prints as itself):

```
ok       =>  
ok     a  =>  a
ok     (a b) c  =>  (a b) c
ok     (a $ b $ c)  =>  (a (b (c)))
ok     (f (g $ h i) j)  =>  (f (g (h i)) j)
ok     (a $)  =>  (a ())
ok     ($ $ a)  =>  (((a)))
ok     (foo$bar $$ a$ $b)  =>  (foo$bar $$ a$ $b)
ok     (a ; one ) (
 b) ; two  =>  (a b)
ok     a;b
c  =>  a c
ok     ; only a comment  =>  
ok     (a	(b)
)  =>  (a (b))
ok     (a $ b ; $ c
 $ d)  =>  (a (b (d)))
ok     (a b  =>  error: missing `)`
ok     ((a) (b  =>  error: missing `)`
ok     (a $ (b  =>  error: missing `)`
ok     a) b  =>  error: unexpected `)`
ok     (a)) (b  =>  error: unexpected `)`
ok     $ a) b  =>  error: unexpected `)`
ok     $ a  =>  error: missing `)` after `$`
ok     (a $ b  =>  error: missing `)` after `$`
ok     (a) $ b ; )  =>  error: missing `)` after `$`
```

[RAN] The same command, `$S --interpret syntax.sl read.sl show.sl tests.sl < /dev/null`, and
`$M --no-extern syntax.sl read.sl show.sl tests.sl < /dev/null` each piped to `md5sum` print
`533749c8d687762a3123277d0429637c`.

**The real readers, observed through a macro.** `diff/showargs.sl` defines a macro `show-args` whose
expansion is a string literal showing the `Raw` arguments the reader handed it, so
`(show-args a $ b $ c)` as a program prints what each implementation's reader made of `a $ b $ c`.
[RAN] `printf '(show-args a $ b $ c)' > case.sl; $M diff/showargs.sl case.sl` and
`$S --interpret diff/showargs.sl case.sl` both print `"a (b (c))"`.

**Twenty-two texts, three readers.** [RAN] `diff/run.sh` prints 22 blocks, all headed `AGREE`
(`diff/run.sh | grep -c '^AGREE'` prints 22, `grep -c '^DIFFER'` prints 0). Thirteen are accepted texts
wrapped in `(show-args ...)`, compared form for form; nine are rejected texts given as the whole file,
compared by message. Two blocks as printed:

```
AGREE
  text      : \(show-args\ x\ \$\ \(y\ \$\ z\)\ w\)
  prototype : (show-args x ((y (z)) w))
  main.exe  : (show-args x ((y (z)) w))
  slc       : (show-args x ((y (z)) w))
AGREE
  text      : \(a\ \$\ \(b
  prototype : error: missing `)`
  main.exe  : error: missing `)`
  slc       : error: missing `)`
```

**The repository's own files.** `diff/corpus.py` takes every file of `tests/`, `mini/`, `std/`, and
`stlc/`, skips those containing `"`, `#\`, or `;!`, wraps the rest in one `(show-args ...)` call,
and compares the prototype's forms with what the macro shows under `$M` and `$S`, a numeral shown as
`<literal>` on both sides.
[RAN] `python3 diff/corpus.py 2 > diff/corpus.log`; the log ends
`files: 1369 {'accepted': 1130, 'skipped': 232, 'rejected': 2, 'DIFFER': 5}` and `exit 0`. The two
rejected by all three are `tests/indent_surplus_bad.sl` (``unexpected `)` ``) and
`tests/indent_unclosed_bad.sl` (``missing `)` ``). The five that differ are
`tests/reserved_name_bad.sl`, `reserved_name_def_bad.sl`, `reserved_name_field_bad.sl`,
`reserved_name_lvl_bad.sl`, and `reserved_name_param_bad.sl`: both implementations reject a name
beginning with `__` while reading, and the subset reads it as an atom.
Limits of this comparison: the wrapper puts every file inside one enclosing form, so it says nothing
about a `$` at a file's top level, and it compares shown text, not trees.

## 8. Do the lemmas have teeth

[RAN] `mutations/run.sh` weakens one rule at a time and re-checks; first lines of each result:

```
M0 unmutated: syntax.sl proof.sl
  exit 0
M1 a comment may skip a newline: m1-syntax.sl proof.sl
proof.sl:33:119: error: argument 2, `a`, of `char-apart-irrefl`: type mismatch: expected `(Apart (Char) CharLt (MkChar (MkU8 10 __1)) (MkChar (MkU8 10 __1)))`, got `(Char)`
M2 a word may stop at any character: m2-syntax.sl proof.sl
proof.sl:43:101: error: argument 5, `p`, of `class-fn`: type mismatch: expected `(Class (Cons (Entry) ...` [cut]
M3 a $ form may run to the end of the text: m3-syntax.sl proof.sl
proof.sl:109:7: error: this `let-match` is missing a branch for the following unrefuted constructor:
m3-syntax.sl:98:3: note: value constructor `ItemsDollarEnd`, which is declared here
M4 the reader lets $ consume the ): syntax.sl m4-read.sl
m4-read.sl:92:77: error: argument 4, `p`, of `ParsedOk`: type mismatch: expected `(Items (Cons (Tok) (TDollar) ts) (Cons (Form) (FList inner) (Nil (Form))) (AtEnd))`, got `(Items (Cons (Tok) (TDollar) ts) (Cons (Form) (FList inner) (Nil (Form))) (AtClose after))`
```

M3 is the informative one: a rule that lets a `$` form end at the end of the text overlaps
`FailDollarEnd`, and the exclusion proof stops exactly there. M1 and M2 fail where the proof uses the
removed premise. `M0` also shows that `proof.sl` needs only `syntax.sl`, not the function.

## 9. Line counts

[RAN] `python3 tools/summary.py`:

```
group                                          lines tokens  bytes
relations: character classes                      22    386   1169
relations: tokens                                 45    888   2803
relations: forms                                  23    500   1511
relations: failure                                22    527   1755
result type and goal                              17    345   1211
function: deriving functions                      75   1599   5139
function: termination lemmas                      20    422   1558
lemmas: order irreflexivity                       15    275    862
lemmas: tokens are a function of the text         65   1214   4090
lemmas: items                                     70   1218   4209
lemmas: the three theorems                        30    533   1858
adequacy: relations and goal                      38    910   2960
adequacy: proofs                                  75   1402   5413
```

Lines are non-blank lines and run long (the longest is 156 characters), so tokens are the fairer
measure.

| | lines | tokens |
|---|---|---|
| relations (the four groups) | 112 | 2301 |
| function, with its termination lemmas | 95 | 2021 |
| lemmas for the three theorems | 180 | 3240 |
| lemmas / relations | 1.61 | 1.41 |
| lemmas / function | 1.89 | 1.60 |
| lemmas / (relations + function) | 0.87 | 0.75 |

Without the third theorem (`one-mistake` and `fail-fn`, 39 lines and 694 tokens), "never both" and
"one reading" cost 141 lines and 2546 tokens, 0.59 of relations plus function in tokens. By tokens,
46% of the lemma text is about text to tokens (irreflexivity, class, comment, word, `$`, `Lex`), 38%
about items, and 16% is the three theorems themselves.

Elapsed time. [RAN] `stat -c '%y %n'` on the S4 files shows the first complete version saved at
10:14:19 and `RUN.md` at 10:37:58 on this machine's clock; earlier scratch files were deleted.
[UNKNOWN] How a session's wall clock translates into effort for a person or another agent.

## 10. Formulations compared

**(A) tokenize, then items** is sections 3 to 6.

**(B) printing.** `adequacy-spec.sl` defines, over the same `Form` and `Tok`:

```scheme
(def-adts $ (Prints : ((List (Form)) forms) ((List (Tok)) toks) ((List (Tok)) more) -> Type)
  enum
  (many PrintsNone : (erased (List (Tok)) more) -> (Prints (Nil (Form)) more more))
  (many PrintsAtom : (erased (String) a) (erased (List (Form)) fs) (erased (List (Tok)) toks more) (erased (Prints fs toks more) p)
     -> (Prints (Cons (Form) (FAtom a) fs) (Cons (Tok) (TAtom a) toks) more))
  (many PrintsList : (erased (List (Form)) inner fs) (erased (List (Tok)) toks mid more)
     (erased (Prints inner toks (Cons (Tok) (TClose) mid)) p) (erased (Prints fs mid more) q)
     -> (Prints (Cons (Form) (FList inner) fs) (Cons (Tok) (TOpen) toks) more))
  (many PrintsDollar : (erased (List (Form)) inner) (erased (List (Tok)) toks after) (erased (Prints inner toks (Cons (Tok) (TClose) after)) p)
     -> (Prints (Cons (Form) (FList inner) (Nil (Form))) (Cons (Tok) (TDollar) toks) (Cons (Tok) (TClose) after))))
```

`Prints forms toks more` says `toks` is one way of writing `forms`, followed by `more`. A list is
written with parentheses (`PrintsList`), or, when it is the last item and the enclosing form's `)`
follows, with `$` (`PrintsDollar`). Reading under (B) is `Lex text toks` and `Prints forms toks (Nil)`.

Is (B) workable when many texts read to the same forms? Yes, as a relation and not as a function.
Whitespace and comments never reach it, because `Lex` has already dropped them; `$` against
parentheses is the choice between two rules. What (B) costs and lacks:

- **It is (A) with one base rule instead of two.** [READ syntax.sl:89-99; adequacy-spec.sl:1-10]
  `PrintsAtom`, `PrintsList`, and `PrintsDollar` are `ItemsAtom`, `ItemsOpen`, and `ItemsDollar` with
  the arguments in another order. `PrintsNone` allows
  any `more`; `ItemsEnd` and `ItemsClose` allow only the end or a `)`. Proved both ways:

  ```scheme
  reading-prints : (erased (List (Tok)) toks) (erased (List (Form)) forms)
      (erased (Items toks forms (AtEnd)) p) -> (erased (Prints forms toks (Nil (Tok))) q)
  printing-reads : (erased (List (Tok)) toks) (erased (List (Form)) forms)
      (erased (Prints forms toks (Nil (Tok))) p) -> (erased (Items toks forms (AtEnd)) q)
  ```

  [RAN] the `Adequate` goal runs of section 6. [READ adequacy-proof.sl:1-39] each direction is one
  induction of 12 or 13 lines over a helper `Follows end more` that turns an `Ending` into the tokens
  that follow.
- **"One reading" is not direct for (B).** `Prints` relates the one token `a` both to no forms, with
  `more` that token, and to the form `a`, with `more` empty. So an induction needs the invariant
  "`more` is empty or starts with `)`", which is what `Items` builds in. [INFERENCE] From the rules
  `PrintsNone` and `PrintsAtom`; I proved determinism only through `Items`.
- **(B) gives no failure relation and no reader.** A positive account of "no printing has these
  tokens" has to follow the scan from the left, which is `ItemsFail`. [INFERENCE] I did not find a
  printing-shaped failure relation; I did not search long.
- **At the character level (B) restates (A).** A relation from tokens to texts that allows any
  whitespace and comments must demand that an atom is followed by a delimiter and that a comment ends
  at a newline, which are `WordStop` and `CommentLine`. [INFERENCE] Not built.

What (B) is good for is a statement the owner can check without following a scan. `adequacy-spec.sl`
adds `Spelled toks text`, the text that writes each token followed by one space, with an atom
required to be a non-empty run of word characters other than `$`, and proves:

```scheme
written-reads : (erased (List (Form)) forms) (erased (List (Tok)) toks) (erased (String) text)
    (erased (Prints forms toks (Nil (Tok))) w) (erased (Spelled toks text) s) -> (erased (Reads text forms) r)
```

"Write the forms as tokens in any of the ways `Prints` allows, spell the tokens one space apart, and
the text reads to those forms." With `one-reading` it reads to nothing else. This is the check that a
degenerate `Reads` would fail. [RAN] the `Adequate` goal runs of section 6. Two caveats.
[READ adequacy-proof.sl:41-51] The proof learns the kinds of `(`, `)`, `$`, and space by running
`classify` in run position and asserting the results with `comptime-match`, so it relies on the
evaluator ([QUOTE DESIGN.md:1305-1307 §29] "Every fact derived from a stored value, that is, a
`comptime-match` and everything that follows from the fields it binds, relies on the evaluator having
evaluated correctly."). And it does not prove that every list of forms has a `Spelled` text.

**Recommendation** [INFERENCE, from the above]: keep (A) as the relation the function and the failure
relation are built on; offer `Prints` to the owner as the definition to read, tied to (A) by the
equivalence; treat the round trip as a required companion theorem of any reading relation.

## 11. Checker obstacles

None blocked the work. Every one, with exact text and what I did:

1. **A `subterm` mark is part of an `Fn` type, so a goal cannot name a recursive lemma by an unmarked type.**
   I met this when a `qed` passed a recursive lemma where the goal's `Fn` had no mark. A 21-line
   reproduction is `obstacles/subterm-in-goal.sl`.
   [RAN] `$M obstacles/subterm-in-goal.sl --goal proved` prints
   ``obstacles/subterm-in-goal.sl:21:35: error: argument 2, `halves`, of `MkTheorem`: type mismatch: expected `(Fn (level-of halves) (erased (Nat) n) (erased (Even n) p) -> (erased (Halves n) h))`, got `(Fn (level-of halves) (erased (Nat) n) (subterm erased (Even n) p) -> (erased (Halves n) h))` ``,
   a note, and `--goal proved: FAIL`; `$S` ends in `--goal proved: FAIL` as well.
   [QUOTE DESIGN.md:696-697 §17] "A function's parameters may be marked `subterm`; the marks are part
   of its signature." Workaround: the goal names a non-recursive wrapper (`reading-prints` calls
   `items-prints`), three lines each. The alternative is to write `subterm` in the goal, as the
   verdict spike does; that puts the proof's induction variable into the statement. The `Reader`
   goal's three lemmas are wrappers already.
2. **One goal per unit.** [QUOTE DESIGN.md:3130 §71] "`goal` and `qed` are each allowed only as a bare
   top-level form of a file, at most once per unit." A second theorem over the same relations is a
   second command line, so the relations must sit in a file with no `goal`. [RAN] Earlier in the
   session, with `Read` still in `spec.sl`, a command line that had `read.sl` and not `spec.sl` gave
   ``read.sl:101:57: error: unbound name `Read` ``; I moved `Read` into `syntax.sl`. Not reproducible
   from the final files.
3. **Names taken.** [RAN] Earlier in the session, not reproducible from the final files: ``spec.sl:75:13: warning: declaration of `Stop` shadows a previous binder``
   with `lib/prelude.sl:1347:3: note: shadowed binder is here`; renamed `Ending`.
   [RAN] ``printing-spec.sl:1:65: warning: declaration of `tail` shadows a built-in``; renamed `more`.
4. **A helper I assumed.** [RAN] Earlier in the session: ``tests.sl:34:22: error: unbound name `str-eqb` `` with
   `hint: nearest in scope: str-eq`. [RAN] `grep -n "str-eqb" lib/prelude.sl` prints nothing and
   `grep -n "many str-eqb" self/*.sl` prints `self/base.sl:69`. Used `str-eq`.
5. **Style warnings.** [RAN] `(cd variants/flat-lex && $M spec.sl read.sl proof.sl qed.sl --goal proved)`
   prints nine warnings of the form
   ``proof.sl:55:8: warning: lopsided `match`; flatten it with a `let-match` on `WordMore` ``; I rewrote
   those as `let-match` with absurd branches (§52), which also shortened the proofs. [RAN] Earlier in the session, a first
   layout of the table gave
   `t1.sl:19:3: warning: same indentation (2) as the previous checked line but nesting is 2, expected 1 (matching that line)`;
   reformatted.
6. **`SCons` warns.** Handled by `;! suppress warn SCons` in `read.sl` and around `dollar` in
   `syntax.sl`. [RAN] Neither goal run prints a warning.
7. **Opaque literals, avoided by design.** No rule compares two character literals, so the `Reader`
   goal never needs two literals shown distinct. The round trip needed four class facts and took them
   by `comptime-match` (section 10).

## 12. Where DESIGN.md does not determine what the reader does

For each: the quote, the question, and what the two implementations do. What they do is evidence,
not an answer. `probe` is `diff/probe.sh`, which shows each reader's result for a whole source text.

**Q1. Which characters are whitespace?**
[QUOTE DESIGN.md:41-42 §1] "An atom is any run of characters other than whitespace, parentheses and `;`."
DESIGN.md is silent on the set. [RAN] `grep -n -i "whitespace\|white space\|blank" DESIGN.md` prints
line 42 only.
- Reference: space, tab, carriage return, newline. [READ lib/reader.ml:95-96, 112]
- slc: every byte below `!` (0x21). [READ self/reader.sl:123-126, 176-185]
- [RAN] `probe '(show-args a\fb)' '(show-args a\vb)' '(show-args a\0b)' '(show-args a\x1fb)'`:
  `main.exe` shows one atom each time (`"a\x0cb"`, `"a\x0bb"`, `"a\x00b"`, `"a\x1fb"`), `slc` shows
  `"a b"` each time. `probe '(show-args a\rb)'`: both `"a b"`. `probe '(show-args a\x7fb)'` and
  `'(show-args a\xc2\xa0b)'`: both one atom. `probe '(show-args \xef\xbb\xbfa b)'`: both make a UTF-8
  byte-order mark part of the first atom.
- The prototype follows the reference; the set is one line of `syntax.sl`.

**Q2. What ends a comment's line?**
[QUOTE DESIGN.md:40-41 §1] "A `;` starts a comment that runs to the end of the line."
Silent on whether a lone carriage return ends a line. Both: only newline, or the end of the text.
[READ lib/reader.ml:106; self/reader.sl:302-306] [RAN] `probe '(show-args a ; c\rb\n d)'`: both `"a d"`.

**Q3. Is `;` inside an atom the start of a comment?** Determined: the sentence quoted in Q1 excludes
`;` from atoms. Both agree. [RAN] `diff/run.sh`, text `(show-args a;b` newline `c)`: all three `(show-args a c)`.

**Q4. What is a token?** "Token" is used at DESIGN.md lines 42, 45, 70, and 2171 and never defined.
[RAN] `grep -n -i "token" DESIGN.md`, leaving aside the erased-value and annotation senses.
[QUOTE DESIGN.md:42-43 §1] "A token that begins with `"` is a string literal."
[QUOTE DESIGN.md:2171 §45] "A string literal is `"..."`, starting at the start of a token"
Open points, with both implementations agreeing on each:
- Does a string literal's token end at its closing quote when an atom character follows?
  [RAN] `probe '(show-args "a"b)'`: both `"<literal> b"`, two items. `'(show-args "a""b")'`: both two literals.
- Is `"` an atom character when it is not first? [RAN] `probe '(show-args a"b")'`: both one name, `"a\"b\""`.
- The same for `#"`. [RAN] `probe '(show-args #"a"b)'`: both `"a b"`. `'(show-args x#"a")'`: both one name.
- Is `$` bare straight after a string literal? [RAN] `probe '(show-args "a"$ b)'`: both `"<literal> (b)"`.
  `'(show-args $"a")'`: both one name, `"$\"a\""`.
- Is the raw name `#"$"` a name or the opener? [RAN] `probe '(show-args #"a b" #"" #"_" _ #"$")'`:
  both show `$` as a name. Consistent with [QUOTE DESIGN.md:46 §1] "It is always a name", not stated for `$`.

**Q5. Does `$` directly before `)` make an empty list?** Not stated; it follows from "exactly as `(`
does" [INFERENCE]. Both: yes. [RAN] `diff/run.sh`, text `(show-args a $)`: all three `(show-args a ())`.

**Q6. Can `$` stand at the top level of a file, and what ends it?**
[QUOTE DESIGN.md:69 §2] "If there is no enclosing form, the missing `)` is an error."
So never; nothing ends it. Both reject, with a message that depends on what follows.
[RAN] `diff/run.sh`: `$ a` gives ``missing `)` after `$` `` in all three; `$ a) b` gives ``unexpected `)` ``
in all three. Whether DESIGN.md should say that the end of a file, or a `;! file` pragma, is not a
terminator is a wording question.

**Q7. Which error does a text with several mistakes have?** Silent. Both report the first stray `)`
in text order, else the innermost opener left open, at that opener's position.
[READ lib/reader.ml:158-180; self/reader.sl:413-427]
[RAN] In a scratch file `e.sl`: `((a) (b` gives ``e.sl:1:6: syntax error: missing `)` `` under both;
`(a $ b` gives ``e.sl:1:4: syntax error: missing `)` after `$` `` under both; `$ a $ b` gives
`e.sl:1:5` under both. It matters only if the failure relation is to fix the message, as `one-mistake` does.

**Q8. Where may a pragma stand, and what is it made of?**
[QUOTE DESIGN.md:41 §1] "A `;!` starts a pragma (§4)."
[QUOTE DESIGN.md:137-138 §4] "A `;! warn` must be written between top-level forms."
[QUOTE DESIGN.md:144-145 §4] "The pair may appear at any nesting depth. Text after the name is ignored."
[QUOTE DESIGN.md:159 §4] "Any other word after `;!` is an error."
- `;! file` inside an open form: silent. [RAN] With `case.sl` holding `(show-args a`, `;! file "x.sl"`,
  and ` b)` on three lines, `$M --no-shape-note diff/showargs.sl case.sl` prints
  `case.sl:1:1: warning: this form is never closed` and ``case.sl:1:1: syntax error: missing `)` ``;
  `$S --interpret --no-shape-note diff/showargs.sl case.sl` prints those two lines and then
  ``x.sl:1:3: warning: a `)` here closes more than is open (surplus `)`)`` and
  ``x.sl:1:3: syntax error: unexpected `)` ``.
- May a pragma follow code on its line? §4 says "A pragma line". [RAN]
  `probe '(show-args a ;! suppress warn SCons\n b)\n;! restore warn SCons\n'`: both read `"a b"`.
- Does `;!` end an atom as `;` does? [RAN] `probe '(show-args foo;! suppress warn SCons\n b)'`: both `"foo b"`.
- Is the space after `;!` required? [RAN] `probe '(show-args a ;!suppress warn SCons\n b ;!restore warn SCons\n)'`: both `"a b"`.
- `;!` with no word: not covered by the line-159 sentence. [RAN] `probe '(show-args a ;!\n b)'`: both
  ``syntax error: a pragma needs a word after `;!` ``.
- `;;!` is a comment in both. [RAN] `probe '(show-args a ;;! bogus\n b)'`: both `"a b"`.
- A pragma inside a `$` form does not end the form. [RAN]
  `probe '(show-args a $ b\n;! suppress warn SCons\n c)\n'`: both `"a (b c)"`.
- `;! warn` inside a form: as §4 says. [RAN] `probe '(show-args a\n;! warn SCons hello\n b)'`: both
  ``syntax error: `;! warn` must be written between top-level forms``.
- What a pragma's words are, and whether NAME may be a raw name: silent.
  [READ lib/reader.ml:75-90; self/reader.sl:272-301] both split the line on blanks and accept `#"..."` as a word.

**Q9. An all-digit atom with a leading zero.**
[QUOTE DESIGN.md:2165-2166 §45] "A numeral is an atom made only of digits, with no leading zero: `0` or `42`."
Is `007` an error or a name? [RAN] `probe '(show-args 007)'`: both `syntax error: 007 has a leading zero`.

**Q10. Character literals.**
[QUOTE DESIGN.md:2167-2171 §45] "A character literal is `#\c` for a single byte `c` that the word
syntax admits, or `#\space`, `#\newline`, `#\tab` or `#\xHH`, where `HH` is two hexadecimal digits.
`#\(`, `#\)` and `#\;` must be written in the hex form."
- "The word syntax" is not defined. [RAN] `grep -n -i "word syntax" DESIGN.md` prints lines 2168 and 2224 only.
- Is an atom that begins `#\` and is no character literal an error or a name? [RAN]
  `probe '(show-args #\\ab)'`: both `syntax error: malformed character literal #\ab`; the same for `#\xZZ` and for `#\` alone.
  `probe '(show-args #x #)'`: both read two names.

**Q11. Is a name beginning with `__` refused by the reader or by the elaborator?**
[QUOTE DESIGN.md:55-57 §1] "A name written without `#"` may not begin with `__`; such a name is written raw."
[RAN] `probe '(show-args __x)'`: both ``syntax error: `__x` begins with `__`, which is reserved for the compilers' messages; write it `#"__x"` ``.
`'(show-args a__b _ __)'`: both refuse `__` and nothing before it.

**Q12. What an unknown escape or an unterminated string is.** §45 lists the escapes and is silent on
other backslash sequences and on a missing closing quote. [RAN] `probe '(show-args "a\\qb")'`: both
`syntax error: unknown escape \q`. `'(show-args "abc)'`: both `syntax error: unterminated string literal`.

**Q13. What tree does reading produce?**
[QUOTE DESIGN.md:2771-2772 §63] "`Raw` is `extern` so that its representation is the reader's own syntax tree"
[QUOTE DESIGN.md:2779-2781 §63] "each top-level form of the source has its literals interned and
replaced by such handles just before it is elaborated. So `Raw` has no literal constructor"
So the tree between reading and interning has literal leaves and is not `Raw`; DESIGN.md does not
name it. [READ lib/reader.ml:7; self/reader.sl:41-49] each implementation has its own (`raw` with
`Nat`, `Char`, `Str`; `Syn` with `RNat`, `RChr`, `RString`). A reading relation needs this type fixed,
or needs interning made part of reading.

**Q14. Positions.**
[QUOTE DESIGN.md:1997-1998 §42] "`Pos`: `NoPos`, or `MkPos` of a file (`String`), a line and a column (`Nat`)."
Silent on whether line and column start at 0 or 1, on the column's unit, and on which character a
form's position is, except [QUOTE DESIGN.md:2738-2739 §62] "the position of the call's opening `(` or `$`"
and [QUOTE DESIGN.md:151 §4] "its lines counted from 1 after the pragma".
[RAN] `grep -n -i "column" DESIGN.md` prints lines 976 and 1998 only.
[READ lib/reader.ml:47] the reference counts both from one, in bytes, at a token's first character.
ASSUMPTIONS.md item 194 records that as a session's choice.

**Q15. When is a file's text read?** Silent.
[RAN] `grep -n -i "is read\|are read\|being read\|the reader" DESIGN.md` finds lines 149, 156, 1926, and 2772 that concern reading, none about order.
- Within a file both read everything first. [RAN] A file `o4.sl` holding
  `(compile-warn "first form elaborated")` and then `(a b`: `$M --no-shape-note o4.sl` and
  `$S --interpret --no-shape-note o4.sl` both print only `o4.sl:2:1: warning: this form is never closed`
  and ``o4.sl:2:1: syntax error: missing `)` ``; the `compile-warn` never fires.
- Across files, one at a time. [RAN] `o5.sl` holding `(compile-warn "file one elaborated")` and `o3.sl`
  holding `(a b`: `$M --no-shape-note o5.sl o3.sl` prints `o5.sl:1:1: warning: file one elaborated` and
  then the syntax error of `o3.sl`; `$S` the same.
- After an elaboration error in the first file, the reference stops and slc goes on to report the
  second file's syntax error as well. [RAN] `o2.sl` holding `(undefined-thing)`, then `o3.sl`.
This decides what "the source code is rejected" is a property of: a file's whole text, or a prefix.

**Q16. Is acceptance affected by warnings?**
[QUOTE DESIGN.md:161-163 §4] "Warnings go to standard error and do not stop elaboration.
`--warnings-as-errors` makes a run that warns fail; a silenced warning does not count (MANUAL.md)."
Both implementations warn about indentation before they report a reading error. [RAN] In a scratch
file `e.sl` holding `(a b`, `$M --no-shape-note e.sl` and `$S --interpret --no-shape-note e.sl` both
print `e.sl:1:1: warning: this form is never closed` before ``e.sl:1:1: syntax error: missing `)` ``.
Under that flag a theorem about acceptance would have to include those warnings, or be stated
without the flag.

## 13. What the full reader would add

Each item is outside the prototype. Sizes are [INFERENCE] from the rules each would need, not measured.

- **String literals.** [QUOTE DESIGN.md:2171-2174 §45] "A string literal is `"..."`, starting at the
  start of a token, with the escapes `\n`, `\t`, `\"`, `\\` and `\xHH`, where `HH` is two hexadecimal
  digits giving one byte. Any other byte, including a newline, stands for itself."
  Adds a string-body relation (closing quote, four plain escapes, the hex escape with a hex-digit
  relation, any other byte), a token and a leaf for strings, and a first-character class that differs
  from the continuation class, since `"` is special only at a token's start (Q4). Adds the first
  lexical failures (unterminated, unknown escape), so `Lex` stops being total: a `LexFails` relation
  and its exclusion lemma, which this subset did not need at all.
- **Raw names.** [QUOTE DESIGN.md:44-46 §1] "A token `#"..."` is a raw name: the string's bytes, read
  as a string literal (§45), whatever they are." Reuses the string body; one more token start.
- **Numerals.** [QUOTE DESIGN.md:43-44 §1] "Atoms made only of digits, and atoms of the form `#\c`,
  are numeral and character literals (§45)." A relation from a digit string to its `Nat`, the
  leading-zero rule (Q9), and so a classification of every word: numeral, character literal, `_`,
  name, or error.
- **Character literals.** The quote of Q10. Five spellings and a malformed-literal failure.
- **`_`.** [QUOTE DESIGN.md:2774-2775 §63] "`RawWild` is a `_`; a raw name `#"_"` is a `RawSymbol` (§1)." One leaf.
- **The `__` rule.** The quote of Q11. One failure; it is the whole of the corpus differences in section 7.
- **Pragmas.** [QUOTE DESIGN.md:128 §4] "A pragma line `;! warn NAME message` names a type constructor, a value",
  with the quotes of Q8 and [QUOTE DESIGN.md:149 §4] "`;! file "name"` ends the file being read and starts one named `name`."
  Adds a pragma-line relation; a top-level sequence relation distinct from nested `Items`, since
  `;! warn` is allowed only there; the open and closed `suppress` regions threaded through reading,
  with two more failures ([QUOTE DESIGN.md:145-147 §4] "A second `suppress` for a name that is already
  open, or a `restore` with no open `suppress`, is an error."); and a source that is a list of named files.
- **Positions.** The quotes of Q14. A line and a column threaded through every `Lex` rule, and a
  position on every token, form, and mistake.
- **The output type.** Q13.

[INFERENCE] My guess is that the full reader's relations, function, and lemmas are each three to
five times this subset's, with the lemmas growing most because lexical failure adds an exclusion
proof the subset lacks. Basis: the rule counts above, and [READ self/reader.sl:1-449] slc's reader
proper being about 450 lines against the 75 of this prototype's functions. Checkable only by building it.

## 14. Things I am least sure of

- **That the relation says what §1 and §2 mean.** The mapping in section 3 is my reading. The
  evidence is agreement with the two implementations (22 texts, 1132 repository files, the probes),
  which shows agreement with them, not with the owner's intent.
- **The whitespace set.** I took the reference's. slc's differs (Q1), and neither is DESIGN.md.
- **Treating `;!` as a comment and literals as atoms** is a simplification that changes meaning: the
  prototype accepts texts both implementations reject (the five `__` files, `007`, `(a ;! bogus` newline `b)`)
  and misreads any text with a string literal that holds a parenthesis or a `;`.
  [RAN] `probe '(show-args "a ; b" c)'`: the prototype prints ``error: missing `)` `` where both implementations read two items.
- **The size estimate for the full reader** (section 13) is a guess from rule counts.
- **Whether the owner counts recursion through `(subterm s)` proofs as fuel-free.** I do, because it
  is the language's own termination check and slc's reader uses it; the task's wording allows it.
- **The stack limit** (section 5) may matter more than I have weighed: the prototype overflows on a
  360 KB text that both implementations read, and I did not build the constant-stack version.
- **The round trip relies on the evaluator** for four facts, and does not show every list of forms
  can be spelled.
- **The flat-against-indexed comparison** is between one version written first and one written
  second; the second benefited from the first.
- **The corpus comparison** compares shown text after mapping numerals to `<literal>`, inside one
  wrapping form; a difference that both sides print alike would be missed.
- **`one-mistake`** fixes which mistake a text has. The owner may not want the specification to fix
  messages at all; the first two theorems do not depend on it.
