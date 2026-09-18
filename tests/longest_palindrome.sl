; needs: palindrome_relations palindrome_bridge
; expect: (Cons 0 (Cons 1 (Cons 1 (Cons 5 (Cons 4 (Cons 1 (Cons 5 (Nil))))))))
; A naive search for the length of the longest palindromic window of a List (Nat),
; returning the spec's LongestPalindrome proof (palindrome_relations.sl, PART 1)
; through the fused PART 2 relations and the bridge lemmas B1-B5 its proof plan
; lists. Written by a Claude session; the checker, not this comment, is the
; evidence that it is right.

(def-fns _ $ many unsnoc : (erased Type A) (subterm many (List A) xs) (erased (Nat) n) (erased (Length A xs (Succ n)) l) ->
    (many (List A) inner) (many A y) (erased (Concat A inner (Cons _ y (Nil A)) xs) q) (erased (Length A inner n) li)
  (match many xs _
    ((Nil a) (match erased l _))
    ((Cons a x rest)
      (match erased l _
        ((LCons a2 x2 rest2 n2 p)
          (match many rest _
            ((Nil a3) (match erased p _ ((LNil a4) (values (Nil _) x (CatNil _ (Cons _ x (Nil _))) (LNil _)))))
            ((Cons a3 x3 rest3)
              (match erased p _
                ((LCons a4 x4 rest4 n1 p1)
                  (let (many inner) (many y) (erased q) (erased li) (unsnoc _ rest _ p))
                  (values (Cons _ x inner) y (CatCons _ x inner (Cons _ y (Nil _)) rest q) (LCons _ x inner n1 li)))))))))))

(def-adts
  (PalDec : ((List (Nat)) w) -> Type
    enum
    (many IsPal : (erased (List (Nat)) w) (erased (Palindrome (Nat) w) p) -> (PalDec w))
    (many IsNotPal : (erased (List (Nat)) w) (erased (NotPalindrome w) np) -> (PalDec w))))

(def-fns _ $ many pal-dec : (subterm many (Nat) n) (many (List (Nat)) w) (erased (Length (Nat) w n) l) -> (many (PalDec w) d)
  (match many n _
    ((Zero) (match erased l _ ((LNil a) (IsPal _ (PalNil _)))))
    ((Succ n1)
      (match many n1 _
        ((Zero) (match erased l _ ((LCons a x rest n2 p) (match erased p _ ((LNil a2) (IsPal _ (PalOne _ x)))))))
        ((Succ n2)
          (match many w _
            ((Nil a) (match erased l _))
            ((Cons a x withx)
              (match erased l _
                ((LCons a2 x2 withx2 n3 p)
                  (let (many inner) (many y) (erased q) (erased li) (unsnoc _ withx _ p))
                  (match many (nat-cmp x y) _
                    ((CLt t r a3 b lt) (IsNotPal _ (NotPalEnds x y inner withx q (ApartLt x y lt))))
                    ((CGt t r a3 b gt) (IsNotPal _ (NotPalEnds x y inner withx q (ApartGt x y gt))))
                    ((CEq t r a3)
                      (match many (pal-dec n2 inner li) _
                        ((IsPal w2 p2) (IsPal _ (PalWrap _ x inner withx p2 q)))
                        ((IsNotPal w2 np2) (IsNotPal _ (NotPalInner x inner withx q np2)))))))))))))))

(def-adts
  (HasDec : ((List (Nat)) xs) ((Nat) n) -> Type
    enum
    (many Has : (erased (List (Nat)) xs) (erased (Nat) n) (erased (HasPalindromeOfLength xs n) h) -> (HasDec xs n))
    (many HasNot : (erased (List (Nat)) xs) (erased (Nat) n) (erased (NoPalindromeOfLengthF xs n) np) -> (HasDec xs n))))

(def-fns _ $ many has-dec : (many (Nat) n) (subterm many (List (Nat)) xs) -> (many (HasDec xs n) d)
  (match many (take-dec _ n xs) _
    ((TooShort a n0 xs0 len l short) (HasNot _ _ (SlideShort xs n len l short)))
    ((Took a n0 xs0 w tk)
      (match many (pal-dec n w (take-length _ _ _ _ tk)) _
        ((IsPal w0 p) (Has _ _ (HasHere xs n w tk p)))
        ((IsNotPal w0 np)
          (match many xs _
            ((Nil a2) (match erased tk _ ((TakeZero a3 xs3) (match erased np _))))
            ((Cons a2 x rest)
              (match many (has-dec n rest) _
                ((Has xs2 n2 h) (Has _ _ (HasThere x rest n h)))
                ((HasNot xs2 n2 np2) (HasNot _ _ (SlideStep n x rest w tk np np2)))))))))))

(def-fns _ $ many search : (subterm many (Nat) k) (many (List (Nat)) xs) (erased (NoLargerPalindromeF xs k) nl) ->
    (many (Nat) n) (erased (LongestPalindromeF xs n) p)
  (match many k _
    ((Zero) (values (Zero) (IsLongestF xs (Zero) (HasHere xs (Zero) (Nil _) (TakeZero _ xs) (PalNil _)) nl)))
    ((Succ k1)
      (match many (has-dec k xs) _
        ((Has xs0 k0 h) (values k (IsLongestF xs k h nl)))
        ((HasNot xs0 k0 np) (search k1 xs (NoLargerStepF xs k1 np nl)))))))

(def-fns _ $ many longest-palindrome-f : (many (List (Nat)) xs) -> (many (Nat) n) (erased (LongestPalindromeF xs n) p)
  (let (many len) (erased l) (list-length _ xs))
  (search len xs (NoLargerDoneF xs len len l (lt-succ len))))

(def-fns _ $ many longest-palindrome : (many (List (Nat)) xs) -> (many (Nat) n) (erased (LongestPalindrome xs n) q)
  (let (many n) (erased p) (longest-palindrome-f xs))
  (values n (longest-bridge _ _ p)))

(let (many n0) (erased q0) (longest-palindrome (Nil _)))
(let (many n1) (erased q1) (longest-palindrome (Cons _ 7 $ Nil _)))
(let (many n2) (erased q2) (longest-palindrome (Cons _ 1 $ Cons _ 2 $ Nil _)))
(let (many n3) (erased q3) (longest-palindrome (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 2 $ Cons _ 1 $ Cons _ 4 $ Nil _)))
(let (many n4) (erased q4) (longest-palindrome (Cons _ 1 $ Cons _ 2 $ Cons _ 2 $ Cons _ 1 $ Nil _)))
(let (many n5) (erased q5) (longest-palindrome (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 4 $ Cons _ 5 $ Nil _)))
(let (many n6) (erased q6) (longest-palindrome (Cons _ 3 $ Cons _ 1 $ Cons _ 1 $ Cons _ 3 $ Cons _ 1 $ Cons _ 1 $ Nil _)))

(Cons _ n0 $ Cons _ n1 $ Cons _ n2 $ Cons _ n3 $ Cons _ n4 $ Cons _ n5 $ Cons _ n6 $ Nil _)
