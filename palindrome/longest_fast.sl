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
              (match many (decide-palindrome-fast w) _
                ((PD2Yes a2 p) (HDYes (Nil (Nat)) n (HasHere (Nil (Nat)) n w tk p)))
                ((PD2No a2 np) (match erased np _))))))
        ((TkShort n1c xs1c len lp sp) (HDNo (Nil (Nat)) n (SlideShort (Nil (Nat)) n len lp sp)))))
    ((Cons a x xs1)
      (match many (decide-take n (Cons (Nat) x xs1)) _
        ((TkYes n1 xsb w tk)
          (match many (decide-palindrome-fast w) _
            ((PD2Yes a2 p) (HDYes (Cons (Nat) x xs1) n (HasHere (Cons (Nat) x xs1) n w tk p)))
            ((PD2No a2 np)
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
