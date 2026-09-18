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

(def-fns _ $ many pal-length : (subterm many (List (Nat)) xs) ->
    (many (Nat) n) (erased (Length (Nat) xs n) p)
  (match many xs _
    ((Nil a) (values (Zero) (LNil (Nat))))
    ((Cons a x rest)
      (let (many n) (erased p) (pal-length rest))
      (values (Succ n) (LCons (Nat) x rest n p)))))

; Remove the last element of a nonempty list. The length certificate
; supplies the strict decrease for the later onion-peeling recursion.
(def-fns _ $ many pal-unsnoc : (subterm many (List (Nat)) xs)
    (erased (Nat) n) (erased (Length (Nat) xs (Succ n)) len) ->
    (many (List (Nat)) inner) (many (Nat) last)
    (erased (Length (Nat) inner n) ilen)
    (erased (Concat (Nat) inner (Cons (Nat) last (Nil (Nat))) xs) cat)
  (match many xs _
    (absurd (Nil a) (match erased len (((False) f))))
    ((Cons a x rest)
      (match erased len _
        ((LCons b y tail k plen)
          (match many rest _
            ((Nil b)
              (match erased plen _
                ((LNil c)
                  (values (Nil (Nat)) x (LNil (Nat))
                    (CatNil (Nat) (Cons (Nat) x (Nil (Nat))))))))
            ((Cons b y tail)
              (match erased plen _
                ((LCons c z tail2 k2 plen2)
                  (let (many inner) (many last) (erased ilen) (erased cat)
                    (pal-unsnoc rest k2 plen))
                  (values (Cons (Nat) x inner) last
                    (LCons (Nat) x inner k2 ilen)
                    (CatCons (Nat) x inner (Cons (Nat) last (Nil (Nat))) rest cat)))))))))))

(def-adts
  (PalDecision : ((List (Nat)) xs) -> Type enum
    (many PalYes : (erased (List (Nat)) xs)
      (erased (Palindrome (Nat) xs) p) -> (PalDecision xs))
    (many PalNo : (erased (List (Nat)) xs)
      (erased (NotPalindrome xs) p) -> (PalDecision xs))))

(def-fns _ $ many pal-decide : (subterm erased (Nat) n)
    (many (List (Nat)) xs) (erased (Length (Nat) xs n) len) ->
    (many (PalDecision xs) decision)
  (match many xs _
    ((Nil a) (PalYes xs (PalNil (Nat))))
    ((Cons a x rest)
      (match erased len _
        ((LCons b y tail k plen)
          (match many rest _
            ((Nil b) (PalYes xs (PalOne (Nat) x)))
            ((Cons b y tail)
              (match erased plen _
                ((LCons c z tail2 k2 plen2)
                  (let (many inner) (many last) (erased ilen) (erased cat)
                    (pal-unsnoc rest k2 plen))
                  (match many (nat-cmp x last) _
                    ((CLt t r v w lt)
                      (PalNo xs (NotPalEnds x last inner rest cat (ApartLt x last lt))))
                    ((CGt t r v w gt)
                      (PalNo xs (NotPalEnds x last inner rest cat (ApartGt x last gt))))
                    ((CEq t r v)
                      (match many (pal-decide k2 inner ilen) _
                        ((PalYes w p) (PalYes xs (PalWrap (Nat) x inner rest p cat)))
                        ((PalNo w p) (PalNo xs (NotPalInner x inner rest cat p)))))))))))))))

; Either take a complete window with its length, or certify that the
; suffix is too short. No partial window is ever tested as a full one.
(def-adts
  (PalTake : ((Nat) n) ((List (Nat)) xs) -> Type enum
    (many PalTaken : (erased (Nat) n) (erased (List (Nat)) xs)
      (many (List (Nat)) w) (erased (Take (Nat) n xs w) tk)
      (erased (Length (Nat) w n) len) -> (PalTake n xs))
    (many PalShort : (erased (Nat) n) (erased (List (Nat)) xs)
      (erased (Nat) len) (erased (Length (Nat) xs len) p)
      (erased (Lt len n) short) -> (PalTake n xs))))

(def-fns _ $ many pal-take : (subterm many (Nat) n)
    (many (List (Nat)) xs) -> (many (PalTake n xs) result)
  (match many n _
    ((Zero) (PalTaken n xs (Nil (Nat)) (TakeZero (Nat) xs) (LNil (Nat))))
    ((Succ k)
      (match many xs _
        ((Nil a) (PalShort n xs (Zero) (LNil (Nat)) (LtZ k)))
        ((Cons a x rest)
          (match many (pal-take k rest) _
            ((PalTaken m tail w tk len)
              (PalTaken n xs (Cons (Nat) x w)
                (TakeSucc (Nat) k x rest w tk) (LCons (Nat) x w k len)))
            ((PalShort m tail len p short)
              (PalShort n xs (Succ len) (LCons (Nat) x rest len p)
                (LtS len k short)))))))))

(def-adts
  (PalWindowsDecision : ((List (List (Nat))) xss) -> Type enum
    (many PalFound : (erased (List (List (Nat))) xss)
      (erased (Exists (List (Nat)) NatPalindrome xss) p) -> (PalWindowsDecision xss))
    (many PalAbsent : (erased (List (List (Nat))) xss)
      (erased (All (List (Nat)) NotPalindrome xss) p) -> (PalWindowsDecision xss))))

; Build the specification's Windows and All/Exists together. The runtime
; result is just the decision tag; xss and both certificates are erased.
(def-fns _ $ many pal-windows : (many (Nat) k)
    (subterm many (List (Nat)) xs) ->
    (erased (List (List (Nat))) xss)
    (erased (Windows (Nat) (Succ k) xs xss) windows)
    (many (PalWindowsDecision xss) decision)
  (match many xs _
    ((Nil a)
      (values (Nil (List (Nat)))
        (WinStop (Nat) (Succ k) xs (Zero) (LNil (Nat)) (LtZ k))
        (PalAbsent (Nil (List (Nat))) (AllNil (List (Nat)) NotPalindrome))))
    ((Cons a x rest)
      (match many (pal-take (Succ k) xs) _
        ((PalShort m tail len p short)
          (values (Nil (List (Nat))) (WinStop (Nat) (Succ k) xs len p short)
            (PalAbsent (Nil (List (Nat))) (AllNil (List (Nat)) NotPalindrome))))
        ((PalTaken m tail w tk len)
          (let (erased ws) (erased wins) (many result) (pal-windows k rest))
          (let (erased xss) (Cons (List (Nat)) w ws))
          (let (erased windows) (WinStep (Nat) (Succ k) x rest w tk ws wins))
          (values xss windows
            (match many (pal-decide (Succ k) w len) (((PalWindowsDecision xss) d))
              ((PalYes v p)
                (PalFound xss (ExHere (List (Nat)) NatPalindrome w ws (IsNatPalindrome w p))))
              ((PalNo v p)
                (match many result _
                  ((PalFound vs found)
                    (PalFound xss (ExThere (List (Nat)) NatPalindrome w ws found)))
                  ((PalAbsent vs absent)
                    (PalAbsent xss (AllCons (List (Nat)) NotPalindrome w ws p absent))))))))))))

; Zero has one empty window at each suffix, including the empty suffix.
(def-fns _ $ erased pal-zero-windows : (subterm erased (List (Nat)) xs) ->
    (erased (List (List (Nat))) xss)
    (erased (Windows (Nat) (Zero) xs xss) windows)
    (erased (Exists (List (Nat)) NatPalindrome xss) found)
  (match erased xs _
    ((Nil a)
      (values (Cons (List (Nat)) (Nil (Nat)) (Nil (List (Nat))))
        (WinEmpty (Nat))
        (ExHere (List (Nat)) NatPalindrome (Nil (Nat)) (Nil (List (Nat)))
          (IsNatPalindrome (Nil (Nat)) (PalNil (Nat))))))
    ((Cons a x rest)
      (let (erased ws) (erased wins) (erased found) (pal-zero-windows rest))
      (values (Cons (List (Nat)) (Nil (Nat)) ws)
        (WinStep (Nat) (Zero) x rest (Nil (Nat)) (TakeZero (Nat) xs) ws wins)
        (ExHere (List (Nat)) NatPalindrome (Nil (Nat)) ws
          (IsNatPalindrome (Nil (Nat)) (PalNil (Nat))))))))

; The invariant says all lengths above n have already been ruled out.
(def-fns _ $ many pal-search : (many (List (Nat)) xs)
    (subterm many (Nat) n) (erased (NoLargerPalindrome xs n) above) ->
    (many (Nat) answer) (erased (LongestPalindrome xs answer) correct)
  (match many n _
    ((Zero)
      (let (erased ws) (erased wins) (erased found) (pal-zero-windows xs))
      (values (Zero) (IsLongest xs (Zero) ws wins found above)))
    ((Succ k)
      (let (erased ws) (erased wins) (many decision) (pal-windows k xs))
      (match many decision _
        ((PalFound vs found) (values n (IsLongest xs n ws wins found above)))
        ((PalAbsent vs absent)
          (pal-search xs k (NoLargerStep xs k (NoPal xs n ws wins absent) above)))))))

(def-fns _ $ many longest-palindrome : (many (List (Nat)) xs) ->
    (many (Nat) n) (erased (LongestPalindrome xs n) correct)
  (let (many len) (erased p) (pal-length xs))
  (pal-search xs len (NoLargerDone xs len len p (lt-succ len))))
