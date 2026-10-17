; Load after pal/palindrome_relations.sl (the standard prelude is enough).
; Example run (includes runtime examples):
;   opam exec -- dune exec bin/main.exe -- pal/palindrome_relations.sl \
;     pal/palindrome_naive.sl tests/palindrome_naive.sl
;
; longest-palindrome : xs -> n, erased (LongestPalindrome xs n)
; Bind the results with:
;   (let (many n) (erased correct) (longest-palindrome xs))
; Tries lengths from length(xs) down to zero, checking every window.
; Peeling the last element costs linear time, so a palindrome check costs
; O(k^2) and the whole search is O(n^4), counting Nat comparisons as O(1).
; With source-model/unbounded Nat comparisons, their cost is additional.
; All certificates and the list of windows are erased. No fuel, axioms,
; reflection assertions, or changes to the specification are needed.

(def-fns _ $ (many pal-length : (subterm many (List (Nat)) xs) ->
    (many (Nat) n) (erased (PalLength (Nat) xs n) p))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Zero) (PalLNil _))))
  (let ((many n) (erased p)) (notail $ pal-length rest))
  (values (Succ n) (PalLCons _ x _ _ p)))

; Remove the last element of a nonempty list. The length certificate
; supplies the strict decrease for the later onion-peeling recursion.
(def-fns _ $ (many pal-unsnoc : (subterm many (List (Nat)) xs)
    (erased (Nat) n) (erased (PalLength (Nat) xs (Succ n)) len) ->
    (many (List (Nat)) inner) (many (Nat) last)
    (erased (PalLength (Nat) inner n) ilen)
    (erased (PalConcat (Nat) inner (Cons (Nat) last (Nil (Nat))) xs) cat))
  (let-match many xs (Cons _ x rest) (absurd (Nil _) len))
  (let-match erased len (PalLCons _ _ _ _ plen))
  (match many rest _
    ((Nil _)
      (let-match erased plen (PalLNil _))
      (values (Nil _) x (PalLNil _)
        (PalCatNil _ _)))
    ((Cons _ _ _)
      (let-match erased plen (PalLCons _ _ _ k2 _))
      (let ((many inner) (many last) (erased ilen) (erased cat))
        (notail $ pal-unsnoc rest k2 plen))
      (values (Cons _ x inner) last
        (PalLCons _ x _ _ ilen)
        (PalCatCons _ x _ _ _ cat)))))

(def-adts
  ((PalDecision : ((List (Nat)) xs) -> Type) enum
    (many PalYes : (erased (List (Nat)) xs)
      (erased (Palindrome (Nat) xs) p) -> (PalDecision xs))
    (many PalNo : (erased (List (Nat)) xs)
      (erased (NotPalindrome xs) p) -> (PalDecision xs))))

(def-fns _ $ (many pal-decide : (subterm erased (Nat) n)
    (many (List (Nat)) xs) (erased (PalLength (Nat) xs n) len) ->
    (many (PalDecision xs) decision))
  (let-match many xs (Cons _ x rest) ((Nil _) (PalYes xs (PalNil _))))
  (let-match erased len (PalLCons _ _ _ _ plen))
  (let-match many rest (Cons _ _ _) ((Nil _) (PalYes xs (PalOne _ x))))
  (let-match erased plen (PalLCons _ _ _ k2 _))
  (let ((many inner) (many last) (erased ilen) (erased cat))
    (pal-unsnoc rest k2 plen))
  (let-match many (nat-cmp x last) (CEq _ _ _)
    ((CLt _ _ _ _ lt)
      (PalNo xs (NotPalEnds x last _ _ cat (ApartLt _ _ lt))))
    ((CGt _ _ _ _ gt)
      (PalNo xs (NotPalEnds x last _ _ cat (ApartGt _ _ gt)))))
  (match many (notail $ pal-decide k2 inner ilen) _
    ((PalYes _ p) (PalYes xs (PalWrap _ x _ _ p cat)))
    ((PalNo _ p) (PalNo xs (NotPalInner x _ _ cat p)))))

; Either take a complete window with its length, or certify that the
; suffix is too short. No partial window is ever tested as a full one.
(def-adts
  ((PalTake : ((Nat) n) ((List (Nat)) xs) -> Type) enum
    (many PalTaken : (erased (Nat) n) (erased (List (Nat)) xs)
      (many (List (Nat)) w) (erased (Take (Nat) n xs w) tk)
      (erased (PalLength (Nat) w n) len) -> (PalTake n xs))
    (many PalShort : (erased (Nat) n) (erased (List (Nat)) xs)
      (erased (Nat) len) (erased (PalLength (Nat) xs len) p)
      (erased (Lt len n) short) -> (PalTake n xs))))

(def-fns _ $ (many pal-take : (subterm many (Nat) n)
    (many (List (Nat)) xs) -> (many (PalTake n xs) result))
  (let-match many n (Succ k) ((Zero) (PalTaken n xs (Nil _) (TakeZero _ xs) (PalLNil _))))
  (let-match many xs (Cons _ x rest) ((Nil _) (PalShort n xs (Zero) (PalLNil _) (LtZ k))))
  (match many (notail $ pal-take k rest) _
    ((PalTaken _ _ w tk len)
      (PalTaken n xs (Cons _ x w)
        (TakeSucc _ _ x _ _ tk) (PalLCons _ x _ _ len)))
    ((PalShort _ _ _ p short)
      (PalShort n xs _ (PalLCons _ x _ _ p)
        (LtS _ _ short)))))

(def-adts
  ((PalWindowsDecision : ((List (List (Nat))) xss) -> Type) enum
    (many PalFound : (erased (List (List (Nat))) xss)
      (erased (Exists (List (Nat)) NatPalindrome xss) p) -> (PalWindowsDecision xss))
    (many PalAbsent : (erased (List (List (Nat))) xss)
      (erased (All (List (Nat)) NotPalindrome xss) p) -> (PalWindowsDecision xss))))

; Build the specification's Windows and All/Exists together. The runtime
; result is just the decision tag; xss and both certificates are erased.
(def-fns _ $ (many pal-windows : (many (Nat) k)
    (subterm many (List (Nat)) xs) ->
    (erased (List (List (Nat))) xss)
    (erased (Windows (Nat) (Succ k) xs xss) windows)
    (many (PalWindowsDecision xss) decision))
  (let-match many xs (Cons _ x rest)
    ((Nil _)
      (values (Nil _)
        (WinStop _ _ xs (Zero) (PalLNil _) (LtZ k))
        (PalAbsent (Nil _) (AllNil _ NotPalindrome)))))
  (let-match many (pal-take (Succ k) xs) (PalTaken _ _ w tk len)
    ((PalShort _ _ len p short)
      (values (Nil _) (WinStop _ _ xs len p short)
        (PalAbsent (Nil _) (AllNil _ NotPalindrome)))))
  (let ((erased ws) (erased wins) (many result)) (notail $ pal-windows k rest))
  (let ((erased xss)) (Cons _ w ws))
  (let ((erased windows)) (WinStep _ _ x rest w tk ws wins))
  (values xss windows
    (match many (pal-decide _ w len) (((PalWindowsDecision xss) d))
      ((PalYes _ p)
        (PalFound xss (ExHere _ NatPalindrome w ws (IsNatPalindrome w p))))
      ((PalNo _ p)
        (match many result _
          ((PalFound _ found)
            (PalFound xss (ExThere _ NatPalindrome w ws found)))
          ((PalAbsent _ absent)
            (PalAbsent xss (AllCons _ NotPalindrome w ws p absent))))))))

; Zero has one empty window at each suffix, including the empty suffix.
(def-fns _ $ (erased pal-zero-windows : (subterm erased (List (Nat)) xs) ->
    (erased (List (List (Nat))) xss)
    (erased (Windows (Nat) (Zero) xs xss) windows)
    (erased (Exists (List (Nat)) NatPalindrome xss) found))
  (let-match erased xs (Cons _ x rest)
    ((Nil _)
      (values (Cons _ (Nil _) (Nil _))
        (WinEmpty _)
        (ExHere _ NatPalindrome (Nil _) (Nil _)
          (IsNatPalindrome (Nil _) (PalNil _))))))
  (let ((erased ws) (erased wins) (erased _)) (pal-zero-windows rest))
  (values (Cons _ (Nil _) ws)
    (WinStep _ (Zero) x rest (Nil _) (TakeZero _ xs) ws wins)
    (ExHere _ NatPalindrome (Nil _) ws
      (IsNatPalindrome (Nil _) (PalNil _)))))

; The invariant says all lengths above n have already been ruled out.
(def-fns _ $ (many pal-search : (many (List (Nat)) xs)
    (subterm many (Nat) n) (erased (NoLargerPalindrome xs n) above) ->
    (many (Nat) answer) (erased (LongestPalindrome xs answer) correct))
  (match many n _
    ((Zero)
      (let ((erased ws) (erased wins) (erased found)) (pal-zero-windows xs))
      (values (Zero) (IsLongest xs (Zero) ws wins found above)))
    ((Succ k)
      (let ((erased ws) (erased wins) (many decision)) (pal-windows k xs))
      (match many decision _
        ((PalFound _ found) (values n (IsLongest xs n ws wins found above)))
        ((PalAbsent _ absent)
          (tail $ pal-search xs k (NoLargerStep xs k (NoPal xs n ws wins absent) above)))))))

(def-fns _ $ (many longest-palindrome : (many (List (Nat)) xs) ->
    (many (Nat) n) (erased (LongestPalindrome xs n) correct))
  (let ((many len) (erased p)) (pal-length xs))
  (pal-search xs len (NoLargerDone xs len len p (lt-succ len))))
