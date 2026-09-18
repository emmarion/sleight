; Proves against palindrome_relations.sl's PART 2 (fused) relations, per
; that file's own PROOF PLAN; the PART1 bridge (B1-B5) is not attempted here.

(def-fns _ $ many unsnoc-len :
    (erased Type A) (many A hd) (erased (Nat) m) (subterm many (List A) tl) (erased (Length A tl m) lp) ->
    (many (List A) inner) (many A last)
    (erased (Concat A inner (Cons A last (Nil A)) (Cons A hd tl)) catp)
    (erased (Length A inner m) ilenp)
  (match many tl _
    ((Nil a)
      (match erased lp _
        ((LNil a2) (values (Nil A) hd (CatNil A (Cons A hd (Nil A))) (LNil A)))))
    ((Cons a hd2 tl2)
      (match erased lp _
        ((LCons a2 x2 rest2 m1 lp1)
          (let (many inner1) (many last1) (erased catp1) (erased ilenp1) (unsnoc-len A hd2 m1 tl2 lp1))
          (values (Cons A hd inner1) last1
                  (CatCons A hd inner1 (Cons A last1 (Nil A)) tl catp1)
                  (LCons A hd inner1 m1 ilenp1)))))))

(def-adts
  (PalDec : ((List (Nat)) xs) -> Type
    enum
    (many PalYes : (erased (List (Nat)) xs) (erased (Palindrome (Nat) xs) p) -> (PalDec xs))
    (many PalNo : (erased (List (Nat)) xs) (erased (NotPalindrome xs) p) -> (PalDec xs))))

(def-fns _ $ many decide-palindrome :
    (many (List (Nat)) xs) (subterm erased (Nat) xn) (erased (Length (Nat) xs xn) xlp) ->
    (many (PalDec xs) d)
  (match many xs _
    ((Nil a) (PalYes (Nil (Nat)) (PalNil (Nat))))
    ((Cons a x withx)
      (match many withx _
        ((Nil a2) (PalYes (Cons (Nat) x (Nil (Nat))) (PalOne (Nat) x)))
        ((Cons a2 y0 tl0)
          (match erased xlp _
            ((LCons a3 x3 withx3 xn1 xlp1)
              (match erased xlp1 _
                ((LCons a4 y03 tl03 xn2 xlp2)
                  (let (many inner) (many lastv) (erased catp) (erased ilenp) (unsnoc-len (Nat) y0 xn2 tl0 xlp2))
                  (match many (nat-cmp x lastv) _
                    ((CLt t r xx yy ltp)
                      (PalNo (Cons (Nat) x withx) (NotPalEnds x lastv inner withx catp (ApartLt x lastv ltp))))
                    ((CGt t r xx yy gtp)
                      (PalNo (Cons (Nat) x withx) (NotPalEnds x lastv inner withx catp (ApartGt x lastv gtp))))
                    ((CEq t r xx)
                      (let (erased sp1) (prove-subterm xn1 xn))
                      (let (erased sp2) (prove-subterm xn2 xn1))
                      (let (erased sp) (subterm-trans sp2 sp1))
                      (match many (decide-palindrome inner (subterm sp) xn2 ilenp) _
                        ((PalYes a5 p) (PalYes (Cons (Nat) x withx) (PalWrap (Nat) x inner withx p catp)))
                        ((PalNo a5 np) (PalNo (Cons (Nat) x withx) (NotPalInner x inner withx catp np)))))))))))))))

(def-fns _ $ many list-len : (subterm many (List (Nat)) xs) -> (many (Nat) n) (erased (Length (Nat) xs n) p)
  (match many xs _
    ((Nil a) (values (Zero) (LNil (Nat))))
    ((Cons a x rest)
      (let (many n1) (erased p1) (list-len rest))
      (values (Succ n1) (LCons (Nat) x rest n1 p1)))))

(def-adts
  (TakeDec : ((Nat) n) ((List (Nat)) xs) -> Type
    enum
    (many TkYes : (erased (Nat) n) (erased (List (Nat)) xs) (many (List (Nat)) w)
        (erased (Take (Nat) n xs w) tk) -> (TakeDec n xs))
    (many TkShort : (erased (Nat) n) (erased (List (Nat)) xs) (erased (Nat) len)
        (erased (Length (Nat) xs len) lp) (erased (Lt len n) sp) -> (TakeDec n xs))))

(def-fns _ $ many decide-take : (many (Nat) n) (subterm many (List (Nat)) xs) -> (many (TakeDec n xs) d)
  (match many n _
    ((Zero) (TkYes (Zero) xs (Nil (Nat)) (TakeZero (Nat) xs)))
    ((Succ n1)
      (match many xs _
        ((Nil a) (TkShort (Succ n1) (Nil (Nat)) (Zero) (LNil (Nat)) (LtZ n1)))
        ((Cons a x xs1)
          (match many (decide-take n1 xs1) _
            ((TkYes n1b xs1b w tk)
              (TkYes (Succ n1) (Cons (Nat) x xs1) (Cons (Nat) x w) (TakeSucc (Nat) n1 x xs1 w tk)))
            ((TkShort n1c xs1c len lp sp)
              (TkShort (Succ n1) (Cons (Nat) x xs1) (Succ len) (LCons (Nat) x xs1 len lp) (LtS len n1 sp)))))))))

(def-adts
  (HasDec : ((List (Nat)) xs) ((Nat) n) -> Type
    enum
    (many HDYes : (erased (List (Nat)) xs) (erased (Nat) n) (erased (HasPalindromeOfLength xs n) h) -> (HasDec xs n))
    (many HDNo : (erased (List (Nat)) xs) (erased (Nat) n) (erased (NoPalindromeOfLengthF xs n) np) -> (HasDec xs n))))

(def-fns _ $ many decide-has-pal : (subterm many (List (Nat)) xs) (many (Nat) n) -> (many (HasDec xs n) d)
  (match many xs _
    ((Nil a)
      (match many (decide-take n (Nil (Nat))) _
        ((TkYes n1 xs1 w tk)
          (match erased tk _
            ((TakeZero a3 xs3)
              (let (many wn) (erased wlp) (list-len w))
              (match many (decide-palindrome w wn wlp) _
                ((PalYes a2 p) (HDYes (Nil (Nat)) n (HasHere (Nil (Nat)) n w tk p)))
                ((PalNo a2 np) (match erased np _))))))
        ((TkShort n1c xs1c len lp sp) (HDNo (Nil (Nat)) n (SlideShort (Nil (Nat)) n len lp sp)))))
    ((Cons a x xs1)
      (match many (decide-take n (Cons (Nat) x xs1)) _
        ((TkYes n1 xsb w tk)
          (let (many wn) (erased wlp) (list-len w))
          (match many (decide-palindrome w wn wlp) _
            ((PalYes a2 p) (HDYes (Cons (Nat) x xs1) n (HasHere (Cons (Nat) x xs1) n w tk p)))
            ((PalNo a2 np)
              (match many (decide-has-pal xs1 n) _
                ((HDYes a3 n3 h) (HDYes (Cons (Nat) x xs1) n (HasThere x xs1 n h)))
                ((HDNo a3 n3 restp) (HDNo (Cons (Nat) x xs1) n (SlideStep n x xs1 w tk np restp)))))))
        ((TkShort n1c xsb len lp sp) (HDNo (Cons (Nat) x xs1) n (SlideShort (Cons (Nat) x xs1) n len lp sp)))))))

(def-fns _ $ many scan :
    (many (List (Nat)) xs) (subterm many (Nat) k) (erased (NoLargerPalindromeF xs k) nlp) ->
    (many (Nat) n) (erased (LongestPalindromeF xs n) proof)
  (match many k _
    ((Zero)
      (values (Zero)
        (IsLongestF xs (Zero) (HasHere xs (Zero) (Nil (Nat)) (TakeZero (Nat) xs) (PalNil (Nat))) nlp)))
    ((Succ k1)
      (match many (decide-has-pal xs k) _
        ((HDYes a nn h) (values k (IsLongestF xs k h nlp)))
        ((HDNo a nn np) (scan xs k1 (NoLargerStepF xs k1 np nlp)))))))

(def-fns _ $ many longest-palindrome : (many (List (Nat)) xs) -> (many (Nat) n) (erased (LongestPalindromeF xs n) proof)
  (let (many n0) (erased lp0) (list-len xs))
  (let (erased nlp0) (NoLargerDoneF xs n0 n0 lp0 (lt-succ n0)))
  (scan xs n0 nlp0))

(let (many one) (Succ (Zero)))
(let (many two) (Succ one))
(let (many xs) (Cons (Nat) one (Cons (Nat) two (Cons (Nat) one (Nil (Nat))))))
(let (many n) (erased proof) (longest-palindrome xs))
n
