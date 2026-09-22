; Relations for the longest-palindromic-substring puzzle, over List (Nat).
; Merged from relations.sl (base) and rel.sl (fused sliding relations).
; Pure inductive data only -- no def-fns, no functions embedded in any type.
; Dependency order: each relation only refers to ones already defined.
;
; Layout:
;   PART 1  the SPEC      -- compositional, meant to be read and trusted.
;   PART 2  FUSED helpers -- same meaning, one induction each, meant to be
;                            proved against. Prove the algorithm correct
;                            w.r.t. PART 2, then bridge to PART 1 once.
;
; Changes vs relations.sl:
;   * Windows gains WinEmpty, so it is now total and correct at n = Zero.
;     That alone makes (LongestPalindrome (Nil (Nat)) (Zero)) inhabited;
;     before, the empty input had no valid answer at all.
;   * Differ removed (nothing used it; NotPalindrome only needs NatApart).
;   * Reverse kept but marked optional (nothing in the spec uses it).
; Only syntax already appearing in the two source files is used.

; =====================================================================
; PART 1 -- SPEC
; =====================================================================

; --- xs ++ ys = zs ---
; NB: named Concat, not Append, to stay clear of the prelude's Append.

(def-adts
  ((Concat : (Type A) ((List A) xs) ((List A) ys) ((List A) zs) -> Type)
    enum
    (many CatNil : (erased Type A) (erased (List A) ys) ->
       (Concat A (Nil A) ys ys))
    (many CatCons : (erased Type A) (erased A x) (erased (List A) rest)
        (erased (List A) ys) (erased (List A) zs)
        (erased (Concat A rest ys zs) p) ->
       (Concat A (Cons A x rest) ys (Cons A x zs)))))

; --- xs reads the same forwards and backwards ("onion peeling") ---
; Nil and singletons are palindromes; wrapping a palindrome in the same
; element at both ends gives a bigger one. One PalWrap per matched pair of
; ends, which is exactly what expand-around-centre style proofs recurse on.

(def-adts
  ((Palindrome : (Type A) ((List A) xs) -> Type)
    enum
    (many PalNil : (erased Type A) -> (Palindrome A (Nil A)))
    (many PalOne : (erased Type A) (erased A x) ->
       (Palindrome A (Cons A x (Nil A))))
    (many PalWrap : (erased Type A) (erased A x) (erased (List A) inner)
        (erased (List A) withx)
        (erased (Palindrome A inner) p)
        (erased (Concat A inner (Cons A x (Nil A)) withx) q) ->
       (Palindrome A (Cons A x withx)))))

; --- positive evidence that two Nats differ ---
; Fixed to Lt rather than taking an arbitrary relation R as a parameter:
; an unconstrained R (anything reflexive) would let NotPalindrome hold of
; real palindromes and make the whole spec vacuous.

(def-adts
  ((NatApart : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many ApartLt : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (NatApart a b))
    (many ApartGt : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) p) -> (NatApart a b))))

; --- xs is NOT a palindrome (mirror image of Palindrome) ---
; Decompose xs as x :: (inner ++ [y]). Either the ends differ (NotPalEnds)
; or they agree and inner is itself not a palindrome (NotPalInner).
; Lists of fewer than two elements can never be shown NotPalindrome.

(def-adts
  ((NotPalindrome : ((List (Nat)) xs) -> Type)
    enum
    (many NotPalEnds : (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) inner)
        (erased (List (Nat)) withx)
        (erased (Concat (Nat) inner (Cons (Nat) y (Nil (Nat))) withx) q)
        (erased (NatApart x y) d) ->
       (NotPalindrome (Cons (Nat) x withx)))
    (many NotPalInner : (erased (Nat) x) (erased (List (Nat)) inner) (erased (List (Nat)) withx)
        (erased (Concat (Nat) inner (Cons (Nat) x (Nil (Nat))) withx) q)
        (erased (NotPalindrome inner) np) ->
       (NotPalindrome (Cons (Nat) x withx)))))

; --- xs has length n ---

(def-adts
  ((Length : (Type A) ((List A) xs) ((Nat) n) -> Type)
    enum
    (many LNil : (erased Type A) -> (Length A (Nil A) (Zero)))
    (many LCons : (erased Type A) (erased A x) (erased (List A) rest) (erased (Nat) n)
        (erased (Length A rest n) p) ->
       (Length A (Cons A x rest) (Succ n)))))

; --- w is the first n elements of xs ---
; Only inhabited when xs has at least n elements.

(def-adts
  ((Take : (Type A) ((Nat) n) ((List A) xs) ((List A) w) -> Type)
    enum
    (many TakeZero : (erased Type A) (erased (List A) xs) -> (Take A (Zero) xs (Nil A)))
    (many TakeSucc : (erased Type A) (erased (Nat) n) (erased A x) (erased (List A) xs)
        (erased (List A) w) (erased (Take A n xs w) t) ->
       (Take A (Succ n) (Cons A x xs) (Cons A x w)))))

; --- xss is exactly the contiguous length-n windows of xs, in order ---
; Slide along xs: take a full window (WinStep), or stop because the suffix
; is too short (WinStop). Exactly one constructor applies at each xs/n:
;   n >= 1, suffix long enough : WinStep   (Take succeeds, Lt fails)
;   n >= 1, suffix too short   : WinStop   (Lt holds, Take impossible)
;   n  = 0, Cons               : WinStep   (Take Zero always succeeds)
;   n  = 0, Nil                : WinEmpty  (Lt len Zero is never satisfiable)
; WinEmpty is the new case: the empty suffix still has one length-0 window,
; so Windows Zero xs has (length xs + 1) empty windows, as it should.

(def-adts
  ((Windows : (Type A) ((Nat) n) ((List A) xs) ((List (List A)) xss) -> Type)
    enum
    (many WinEmpty : (erased Type A) ->
       (Windows A (Zero) (Nil A) (Cons (List A) (Nil A) (Nil (List A)))))
    (many WinStop : (erased Type A) (erased (Nat) n) (erased (List A) xs)
        (erased (Nat) len) (erased (Length A xs len) l) (erased (Lt len n) short) ->
       (Windows A n xs (Nil (List A))))
    (many WinStep : (erased Type A) (erased (Nat) n) (erased A x) (erased (List A) xs)
        (erased (List A) w) (erased (Take A n (Cons A x xs) w) tk)
        (erased (List (List A)) rest) (erased (Windows A n xs rest) r) ->
       (Windows A n (Cons A x xs) (Cons (List A) w rest)))))

; --- every element of xs satisfies P (P a first-class unary TyCtor) ---

(def-adts
  ((All : (Type A) ((TyCtor (A x) -> Type) P) ((List A) xs) -> Type)
    enum
    (many AllNil : (erased Type A) (erased (TyCtor (A x) -> Type) P) ->
       (All A P (Nil A)))
    (many AllCons : (erased Type A) (erased (TyCtor (A x) -> Type) P) (erased A x)
        (erased (List A) rest) (erased (P x) p) (erased (All A P rest) ps) ->
       (All A P (Cons A x rest)))))

; --- some element of xs satisfies P ---
; No Nil case: an empty list never witnesses an existential.

(def-adts
  ((Exists : (Type A) ((TyCtor (A x) -> Type) P) ((List A) xs) -> Type)
    enum
    (many ExHere : (erased Type A) (erased (TyCtor (A x) -> Type) P) (erased A x)
        (erased (List A) rest) (erased (P x) p) ->
       (Exists A P (Cons A x rest)))
    (many ExThere : (erased Type A) (erased (TyCtor (A x) -> Type) P) (erased A x)
        (erased (List A) rest) (erased (Exists A P rest) e) ->
       (Exists A P (Cons A x rest)))))

; --- adapter: Palindrome with A fixed to Nat (constructors can't be curried) ---

(def-adts
  ((NatPalindrome : ((List (Nat)) xs) -> Type)
    enum
    (many IsNatPalindrome : (erased (List (Nat)) xs) (erased (Palindrome (Nat) xs) p) ->
       (NatPalindrome xs))))

; --- no window of length n in xs is a palindrome ---
; Uninhabited at n = Zero and n = 1 on any list that has such a window,
; since length-0 and length-1 windows are always palindromes. Correct.

(def-adts
  ((NoPalindromeOfLength : ((List (Nat)) xs) ((Nat) n) -> Type)
    enum
    (many NoPal : (erased (List (Nat)) xs) (erased (Nat) n) (erased (List (List (Nat))) xss)
        (erased (Windows (Nat) n xs xss) w) (erased (All (List (Nat)) NotPalindrome xss) a) ->
       (NoPalindromeOfLength xs n))))

; --- no window longer than n in xs is a palindrome ---
; Upward induction from n: either xs has at most n elements, so nothing
; longer exists (NoLargerDone: len < Succ n, i.e. len <= n), or length
; (Succ n) is checked explicitly and the rest is deferred one step out.

(def-adts
  ((NoLargerPalindrome : ((List (Nat)) xs) ((Nat) n) -> Type)
    enum
    (many NoLargerDone : (erased (List (Nat)) xs) (erased (Nat) n) (erased (Nat) len)
        (erased (Length (Nat) xs len) l) (erased (Lt len (Succ n)) short) ->
       (NoLargerPalindrome xs n))
    (many NoLargerStep : (erased (List (Nat)) xs) (erased (Nat) n)
        (erased (NoPalindromeOfLength xs (Succ n)) here)
        (erased (NoLargerPalindrome xs (Succ n)) rest) ->
       (NoLargerPalindrome xs n))))

; --- THE ANSWER: n is the length of xs's longest palindromic substring ---
; SOME window of length n is a palindrome, and NO longer window is.
; Empty input: Windows Zero Nil [[]] (WinEmpty), Exists via PalNil,
; NoLargerDone with len = Zero. So LongestPalindrome Nil Zero holds, and
; no other n does (Windows (Succ k) Nil is only ever the empty list).

(def-adts
  ((LongestPalindrome : ((List (Nat)) xs) ((Nat) n) -> Type)
    enum
    (many IsLongest : (erased (List (Nat)) xs) (erased (Nat) n)
        (erased (List (List (Nat))) xss)
        (erased (Windows (Nat) n xs xss) w)
        (erased (Exists (List (Nat)) NatPalindrome xss) e)
        (erased (NoLargerPalindrome xs n) nl) ->
       (LongestPalindrome xs n))))

; =====================================================================
; PART 2 -- FUSED HELPERS (not part of the trusted spec)
; =====================================================================
; Each of these inlines Windows + All/Exists into a single slide along xs,
; so a proof is ONE induction instead of building xss, a Windows proof and
; an All/Exists proof in lockstep. Adapted from rel.sl, with its two holes
; closed: HasHere no longer demands a Cons (so the empty list works), and
; the "differs" evidence is NatApart rather than a free parameter R.

; --- some window of length n in xs is a palindrome ---
; Fuses:  Windows n xs xss  +  Exists NatPalindrome xss.

(def-adts
  ((HasPalindromeOfLength : ((List (Nat)) xs) ((Nat) n) -> Type)
    enum
    (many HasHere : (erased (List (Nat)) xs) (erased (Nat) n) (erased (List (Nat)) w)
        (erased (Take (Nat) n xs w) tk) (erased (Palindrome (Nat) w) p) ->
       (HasPalindromeOfLength xs n))
    (many HasThere : (erased (Nat) x) (erased (List (Nat)) xs) (erased (Nat) n)
        (erased (HasPalindromeOfLength xs n) h) ->
       (HasPalindromeOfLength (Cons (Nat) x xs) n))))

; --- no window of length n in xs is a palindrome ---
; Fuses:  Windows n xs xss  +  All NotPalindrome xss.
; SlideShort mirrors WinStop, SlideStep mirrors WinStep + AllCons.
; (No mirror of WinEmpty: its one window is Nil, which is a palindrome.)

(def-adts
  ((NoPalindromeOfLengthF : ((List (Nat)) xs) ((Nat) n) -> Type)
    enum
    (many SlideShort : (erased (List (Nat)) xs) (erased (Nat) n) (erased (Nat) len)
        (erased (Length (Nat) xs len) l) (erased (Lt len n) short) ->
       (NoPalindromeOfLengthF xs n))
    (many SlideStep : (erased (Nat) n) (erased (Nat) x) (erased (List (Nat)) xs)
        (erased (List (Nat)) w)
        (erased (Take (Nat) n (Cons (Nat) x xs) w) tk)
        (erased (NotPalindrome w) np)
        (erased (NoPalindromeOfLengthF xs n) rest) ->
       (NoPalindromeOfLengthF (Cons (Nat) x xs) n))))

; --- no window longer than n is a palindrome (fused) ---

(def-adts
  ((NoLargerPalindromeF : ((List (Nat)) xs) ((Nat) n) -> Type)
    enum
    (many NoLargerDoneF : (erased (List (Nat)) xs) (erased (Nat) n) (erased (Nat) len)
        (erased (Length (Nat) xs len) l) (erased (Lt len (Succ n)) short) ->
       (NoLargerPalindromeF xs n))
    (many NoLargerStepF : (erased (List (Nat)) xs) (erased (Nat) n)
        (erased (NoPalindromeOfLengthF xs (Succ n)) here)
        (erased (NoLargerPalindromeF xs (Succ n)) rest) ->
       (NoLargerPalindromeF xs n))))

; --- fused answer ---

(def-adts
  ((LongestPalindromeF : ((List (Nat)) xs) ((Nat) n) -> Type)
    enum
    (many IsLongestF : (erased (List (Nat)) xs) (erased (Nat) n)
        (erased (HasPalindromeOfLength xs n) h)
        (erased (NoLargerPalindromeF xs n) nl) ->
       (LongestPalindromeF xs n))))

; =====================================================================
; PART 3 -- OPTIONAL: Reverse, for a sanity lemma only
; =====================================================================
; Nothing above depends on this. Keep it if you want to prove
; Palindrome A xs <-> Reverse A xs xs as evidence the structural
; definition means what it should; delete it otherwise.

(def-adts
  ((Reverse : (Type A) ((List A) xs) ((List A) ys) -> Type)
    enum
    (many RevNil : (erased Type A) -> (Reverse A (Nil A) (Nil A)))
    (many RevCons : (erased Type A) (erased A x) (erased (List A) xs)
        (erased (List A) ys) (erased (List A) zs)
        (erased (Reverse A xs ys) p)
        (erased (Concat A ys (Cons A x (Nil A)) zs) q) ->
       (Reverse A (Cons A x xs) zs))))

; =====================================================================
; PROOF PLAN (lemmas to write as def-fns; not included, syntax unknown)
; =====================================================================
; Bridge, fused -> spec (the only direction correctness needs):
;   B1. windows_total : every n, xs has some xss with Windows (Nat) n xs xss.
;       Needs "Lt len n, or Take n xs w for some w" decided on Length.
;   B2. HasPalindromeOfLength xs n  -> Windows n xs xss -> Exists NatPalindrome xss
;       Needs Take functional (same n, xs => same w) and Windows functional.
;   B3. NoPalindromeOfLengthF xs n  -> NoPalindromeOfLength xs n
;   B4. NoLargerPalindromeF xs n    -> NoLargerPalindrome xs n      (from B3)
;   B5. LongestPalindromeF xs n     -> LongestPalindrome xs n       (B1,B2,B4)
;   B1/B3 return an xss alongside a proof about it, so they need whatever
;   this language offers for a dependent pair; B5's statement does not.
; Sanity (shows the spec is not vacuous or contradictory):
;   S1. Palindrome (Nat) w -> NotPalindrome w -> absurd
;       Needs snoc-injectivity of Concat and irreflexivity of Lt.
;   S2. LongestPalindrome xs n -> LongestPalindrome xs m -> n = m
; Main theorem:
;   every xs : LongestPalindromeF xs (algo xs), then B5.
