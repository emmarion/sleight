; needs: palindrome_relations
; expect: (Cons 0 (Cons 1 (Cons 1 (Cons 5 (Cons 4 (Cons 1 (Cons 5 (Nil))))))))
; A naive search for the length of the longest palindromic window of a List (Nat),
; returning the spec's LongestPalindrome proof (palindrome_relations.sl, PART 1)
; through the fused PART 2 relations and the bridge lemmas B1-B5 its proof plan
; lists. Written by a Claude session; the checker, not this comment, is the
; evidence that it is right.

(def-fns _ $ many list-length : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n) (erased (Length A xs n) l)
  (match many xs _
    ((Nil a) (values (Zero) (LNil A)))
    ((Cons a x rest)
      (let (many n) (erased l) (list-length A rest))
      (values (Succ n) (LCons A x rest n l)))))

(def-fns _ $ many unsnoc : (erased Type A) (subterm many (List A) xs) (erased (Nat) n) (erased (Length A xs (Succ n)) l) ->
    (many (List A) inner) (many A y) (erased (Concat A inner (Cons A y (Nil A)) xs) q) (erased (Length A inner n) li)
  (match many xs _
    ((Nil a) (match erased l _))
    ((Cons a x rest)
      (match erased l _
        ((LCons a2 x2 rest2 n2 p)
          (match many rest _
            ((Nil a3) (match erased p _ ((LNil a4) (values (Nil A) x (CatNil A (Cons A x (Nil A))) (LNil A)))))
            ((Cons a3 x3 rest3)
              (match erased p _
                ((LCons a4 x4 rest4 n1 p1)
                  (let (many inner) (many y) (erased q) (erased li) (unsnoc A rest n1 p))
                  (values (Cons A x inner) y (CatCons A x inner (Cons A y (Nil A)) rest q) (LCons A x inner n1 li)))))))))))

(def-adts
  (PalDec : ((List (Nat)) w) -> Type
    enum
    (many IsPal : (erased (List (Nat)) w) (erased (Palindrome (Nat) w) p) -> (PalDec w))
    (many IsNotPal : (erased (List (Nat)) w) (erased (NotPalindrome w) np) -> (PalDec w))))

(def-fns _ $ many pal-dec : (subterm many (Nat) n) (many (List (Nat)) w) (erased (Length (Nat) w n) l) -> (many (PalDec w) d)
  (match many n _
    ((Zero) (match erased l _ ((LNil a) (IsPal w (PalNil (Nat))))))
    ((Succ n1)
      (match many n1 _
        ((Zero) (match erased l _ ((LCons a x rest n2 p) (match erased p _ ((LNil a2) (IsPal w (PalOne (Nat) x)))))))
        ((Succ n2)
          (match many w _
            ((Nil a) (match erased l _))
            ((Cons a x withx)
              (match erased l _
                ((LCons a2 x2 withx2 n3 p)
                  (let (many inner) (many y) (erased q) (erased li) (unsnoc (Nat) withx n2 p))
                  (match many (nat-cmp x y) _
                    ((CLt t r a3 b lt) (IsNotPal w (NotPalEnds x y inner withx q (ApartLt x y lt))))
                    ((CGt t r a3 b gt) (IsNotPal w (NotPalEnds x y inner withx q (ApartGt x y gt))))
                    ((CEq t r a3)
                      (match many (pal-dec n2 inner li) _
                        ((IsPal w2 p2) (IsPal w (PalWrap (Nat) x inner withx p2 q)))
                        ((IsNotPal w2 np2) (IsNotPal w (NotPalInner x inner withx q np2)))))))))))))))

(def-adts
  (TakeDec : (Type A) ((Nat) n) ((List A) xs) -> Type
    enum
    (many Took : (erased Type A) (erased (Nat) n) (erased (List A) xs) (many (List A) w) (erased (Take A n xs w) tk) ->
       (TakeDec A n xs))
    (many TooShort : (erased Type A) (erased (Nat) n) (erased (List A) xs) (erased (Nat) len)
        (erased (Length A xs len) l) (erased (Lt len n) short) ->
       (TakeDec A n xs))))

(def-fns _ $ many take-dec : (erased Type A) (subterm many (Nat) n) (many (List A) xs) -> (many (TakeDec A n xs) d)
  (match many n _
    ((Zero) (Took A n xs (Nil A) (TakeZero A xs)))
    ((Succ n1)
      (match many xs _
        ((Nil a) (TooShort A n xs (Zero) (LNil A) (LtZ n1)))
        ((Cons a x rest)
          (match many (take-dec A n1 rest) _
            ((Took a2 n2 xs2 w tk) (Took A n xs (Cons A x w) (TakeSucc A n1 x rest w tk)))
            ((TooShort a2 n2 xs2 len l short) (TooShort A n xs (Succ len) (LCons A x rest len l) (LtS len n1 short)))))))))

(def-fns _ $ erased take-length : (erased Type A) (erased (Nat) n) (erased (List A) xs) (erased (List A) w)
    (subterm erased (Take A n xs w) t) -> (erased (Length A w n) l)
  (match erased t _
    ((TakeZero a xs0) (LNil A))
    ((TakeSucc a n1 x xs1 w1 t1) (LCons A x w1 n1 (take-length A n1 xs1 w1 t1)))))

(def-adts
  (HasDec : ((List (Nat)) xs) ((Nat) n) -> Type
    enum
    (many Has : (erased (List (Nat)) xs) (erased (Nat) n) (erased (HasPalindromeOfLength xs n) h) -> (HasDec xs n))
    (many HasNot : (erased (List (Nat)) xs) (erased (Nat) n) (erased (NoPalindromeOfLengthF xs n) np) -> (HasDec xs n))))

(def-fns _ $ many has-dec : (many (Nat) n) (subterm many (List (Nat)) xs) -> (many (HasDec xs n) d)
  (match many (take-dec (Nat) n xs) _
    ((TooShort a n0 xs0 len l short) (HasNot xs n (SlideShort xs n len l short)))
    ((Took a n0 xs0 w tk)
      (match many (pal-dec n w (take-length (Nat) n xs w tk)) _
        ((IsPal w0 p) (Has xs n (HasHere xs n w tk p)))
        ((IsNotPal w0 np)
          (match many xs _
            ((Nil a2) (match erased tk _ ((TakeZero a3 xs3) (match erased np _))))
            ((Cons a2 x rest)
              (match many (has-dec n rest) _
                ((Has xs2 n2 h) (Has xs n (HasThere x rest n h)))
                ((HasNot xs2 n2 np2) (HasNot xs n (SlideStep n x rest w tk np np2)))))))))))

(def-fns _ $ many search : (subterm many (Nat) k) (many (List (Nat)) xs) (erased (NoLargerPalindromeF xs k) nl) ->
    (many (Nat) n) (erased (LongestPalindromeF xs n) p)
  (match many k _
    ((Zero) (values (Zero) (IsLongestF xs (Zero) (HasHere xs (Zero) (Nil (Nat)) (TakeZero (Nat) xs) (PalNil (Nat))) nl)))
    ((Succ k1)
      (match many (has-dec k xs) _
        ((Has xs0 k0 h) (values k (IsLongestF xs k h nl)))
        ((HasNot xs0 k0 np) (search k1 xs (NoLargerStepF xs k1 np nl)))))))

(def-fns _ $ many longest-palindrome-f : (many (List (Nat)) xs) -> (many (Nat) n) (erased (LongestPalindromeF xs n) p)
  (let (many len) (erased l) (list-length (Nat) xs))
  (search len xs (NoLargerDoneF xs len len l (lt-succ len))))

; --- bridge, fused -> spec (the proof plan's B1-B5) ---

(def-fns _ $ erased take-fn : (erased Type A) (erased (Nat) n) (erased (List A) xs) (erased (List A) w1) (erased (List A) w2)
    (subterm erased (Take A n xs w1) t1) (erased (Take A n xs w2) t2) -> (erased (Eq (List A) w1 w2) e)
  (match erased t1 _
    ((TakeZero a xs0) (match erased t2 _ ((TakeZero a2 xs2) (Refl (List A) w1))))
    ((TakeSucc a n1 x xs1 v1 s1)
      (match erased t2 _
        ((TakeSucc a2 n2 x2 xs2 v2 s2)
          (match erased (take-fn A n1 xs1 v1 v2 s1 s2) _ ((Refl t r) (Refl (List A) w1))))))))

(def-fns _ $ erased take-not-short : (erased Type A) (erased (Nat) n) (erased (List A) xs) (erased (List A) w) (erased (Nat) len)
    (subterm erased (Take A n xs w) t) (erased (Length A xs len) l) (erased (Lt len n) short) -> (erased (False) f)
  (match erased t _
    ((TakeZero a xs0) (match erased short _))
    ((TakeSucc a n1 x xs1 w1 t1)
      (match erased l _
        ((LCons a2 x2 xs2 len1 l1)
          (match erased short _
            ((LtS s1 s2 short1) (take-not-short A n1 xs1 w1 len1 t1 l1 short1))))))))

(def-fns _ $ erased has-not-short : (erased (List (Nat)) xs) (erased (Nat) n) (erased (Nat) len)
    (subterm erased (HasPalindromeOfLength xs n) h) (erased (Length (Nat) xs len) l) (erased (Lt len n) short) -> (erased (False) f)
  (match erased h _
    ((HasHere xs0 n0 w tk p) (take-not-short (Nat) n xs w len tk l short))
    ((HasThere x rest n0 h1)
      (match erased l _
        ((LCons a x2 rest2 len1 l1)
          (has-not-short rest n len1 h1 l1 (lt-trans len1 (Succ len1) n (lt-succ len1) short)))))))

(def-fns _ $ erased windows-total : (erased Type A) (erased (Nat) n) (subterm erased (List A) xs) ->
    (erased (List (List A)) xss) (erased (Windows A n xs xss) w)
  (match erased (take-dec A n xs) _
    ((TooShort a n0 xs0 len l short) (values (Nil (List A)) (WinStop A n xs len l short)))
    ((Took a n0 xs0 win tk)
      (match erased xs _
        ((Nil a2) (match erased tk _ ((TakeZero a3 xs3) (values (Cons (List A) (Nil A) (Nil (List A))) (WinEmpty A)))))
        ((Cons a2 x rest)
          (let (erased xss) (erased w) (windows-total A n rest))
          (values (Cons (List A) win xss) (WinStep A n x rest win tk xss w)))))))

(def-fns _ $ erased has-exists : (erased (List (Nat)) xs) (erased (Nat) n) (erased (List (List (Nat))) xss)
    (subterm erased (HasPalindromeOfLength xs n) h) (erased (Windows (Nat) n xs xss) w) ->
    (erased (Exists (List (Nat)) NatPalindrome xss) e)
  (match erased w _
    ((WinEmpty a)
      (match erased h _
        ((HasHere xs0 n0 win tk p)
          (match erased tk _
            ((TakeZero a2 xs2) (ExHere (List (Nat)) NatPalindrome (Nil (Nat)) (Nil (List (Nat))) (IsNatPalindrome win p)))))))
    (absurd (WinStop a n0 xs0 len l short) (has-not-short xs n len h l short))
    ((WinStep a n0 x rest win2 tk2 xss2 r)
      (match erased h _
        ((HasHere xs0 n1 win tk p)
          (match erased (take-fn (Nat) n xs win win2 tk tk2) _
            ((Refl t v) (ExHere (List (Nat)) NatPalindrome win2 xss2 (IsNatPalindrome win p)))))
        ((HasThere x2 rest2 n1 h1)
          (ExThere (List (Nat)) NatPalindrome win2 xss2 (has-exists rest n xss2 h1 r)))))))

(def-fns _ $ erased nopal-windows : (erased (List (Nat)) xs) (erased (Nat) n) (subterm erased (NoPalindromeOfLengthF xs n) np) ->
    (erased (List (List (Nat))) xss) (erased (Windows (Nat) n xs xss) w) (erased (All (List (Nat)) NotPalindrome xss) a)
  (match erased np _
    ((SlideShort xs0 n0 len l short)
      (values (Nil (List (Nat))) (WinStop (Nat) n xs len l short) (AllNil (List (Nat)) NotPalindrome)))
    ((SlideStep n0 x rest win tk np1 rest-np)
      (let (erased xss) (erased w) (erased a) (nopal-windows rest n rest-np))
      (values (Cons (List (Nat)) win xss) (WinStep (Nat) n x rest win tk xss w)
              (AllCons (List (Nat)) NotPalindrome win xss np1 a)))))

(def-fns _ $ erased nolarger-bridge : (erased (List (Nat)) xs) (erased (Nat) n) (subterm erased (NoLargerPalindromeF xs n) nl) ->
    (erased (NoLargerPalindrome xs n) r)
  (match erased nl _
    ((NoLargerDoneF xs0 n0 len l short) (NoLargerDone xs n len l short))
    ((NoLargerStepF xs0 n0 here rest)
      (let (erased xss) (erased w) (erased a) (nopal-windows xs (Succ n) here))
      (NoLargerStep xs n (NoPal xs (Succ n) xss w a) (nolarger-bridge xs (Succ n) rest)))))

(def-fns _ $ erased longest-bridge : (erased (List (Nat)) xs) (erased (Nat) n) (erased (LongestPalindromeF xs n) p) ->
    (erased (LongestPalindrome xs n) q)
  (match erased p _
    ((IsLongestF xs0 n0 h nl)
      (let (erased xss) (erased w) (windows-total (Nat) n xs))
      (IsLongest xs n xss w (has-exists xs n xss h w) (nolarger-bridge xs n nl)))))

(def-fns _ $ many longest-palindrome : (many (List (Nat)) xs) -> (many (Nat) n) (erased (LongestPalindrome xs n) q)
  (let (many n) (erased p) (longest-palindrome-f xs))
  (values n (longest-bridge xs n p)))

(let (many n0) (erased q0) (longest-palindrome (Nil (Nat))))
(let (many n1) (erased q1) (longest-palindrome (Cons (Nat) 7 $ Nil (Nat))))
(let (many n2) (erased q2) (longest-palindrome (Cons (Nat) 1 $ Cons (Nat) 2 $ Nil (Nat))))
(let (many n3) (erased q3) (longest-palindrome (Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 2 $ Cons (Nat) 1 $ Cons (Nat) 4 $ Nil (Nat))))
(let (many n4) (erased q4) (longest-palindrome (Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 2 $ Cons (Nat) 1 $ Nil (Nat))))
(let (many n5) (erased q5) (longest-palindrome (Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 4 $ Cons (Nat) 5 $ Nil (Nat))))
(let (many n6) (erased q6) (longest-palindrome (Cons (Nat) 3 $ Cons (Nat) 1 $ Cons (Nat) 1 $ Cons (Nat) 3 $ Cons (Nat) 1 $ Cons (Nat) 1 $ Nil (Nat))))

(Cons (Nat) n0 $ Cons (Nat) n1 $ Cons (Nat) n2 $ Cons (Nat) n3 $ Cons (Nat) n4 $ Cons (Nat) n5 $ Cons (Nat) n6 $ Nil (Nat))
