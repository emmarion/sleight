; needs: palindrome_relations
; expect: (Cons 0 (Cons 1 (Cons 3 (Cons 4 (Cons 3 (Nil))))))

(def-adts
  (Or : (Type P) (Type Q) -> Type
    enum
    (many InL : (erased Type P) (erased Type Q) (erased P p) -> (Or P Q))
    (many InR : (erased Type P) (erased Type Q) (erased Q q) -> (Or P Q))))

(def-adts
  (TakeDec : ((Nat) n) ((List (Nat)) xs) -> Type
    enum
    (many TakeYes : (erased (Nat) n) (erased (List (Nat)) xs) (many (List (Nat)) w)
        (erased (Take (Nat) n xs w) tk) -> (TakeDec n xs))
    (many TakeNo : (erased (Nat) n) (erased (List (Nat)) xs) (erased (Nat) len)
        (erased (Length (Nat) xs len) l) (erased (Lt len n) short) -> (TakeDec n xs))))

(def-fns _ $ many list-length : (subterm many (List (Nat)) xs) ->
    (many (Nat) n) (erased (Length (Nat) xs n) p)
  (match many xs _
    ((Nil a) (values (Zero) (LNil (Nat))))
    ((Cons a hd tl)
      (let (many n) (erased p) (list-length tl))
      (values (Succ n) (LCons (Nat) hd tl n p)))))

(def-fns _ $ many take-dec : (subterm many (Nat) n) (many (List (Nat)) xs) ->
    (many (TakeDec n xs) d)
  (match many n _
    ((Zero) (TakeYes n xs (Nil (Nat)) (TakeZero (Nat) xs)))
    ((Succ k)
      (match many xs _
        ((Nil a) (TakeNo n xs (Zero) (LNil (Nat)) (LtZ k)))
        ((Cons a hd tl)
          (match many (take-dec k tl) _
            ((TakeYes n0 xs0 w tk)
              (TakeYes n xs (Cons (Nat) hd w) (TakeSucc (Nat) k hd tl w tk)))
            ((TakeNo n0 xs0 len l short)
              (TakeNo n xs (Succ len) (LCons (Nat) hd tl len l) (LtS len k short)))))))))

(def-fns _ $ many unsnoc : (subterm many (List (Nat)) xs) (erased (Nat) m)
    (erased (Length (Nat) xs (Succ m)) l) ->
    (many (Nat) y) (many (List (Nat)) inner)
    (erased (Concat (Nat) inner (Cons (Nat) y (Nil (Nat))) xs) q)
    (erased (Length (Nat) inner m) li)
  (match many xs _
    ((Nil a) (match erased l _))
    ((Cons a hd tl)
      (match many tl _
        ((Nil a2)
          (match erased l _
            ((LCons b1 x1 r1 n1 p1)
              (match erased p1 _
                ((LNil b2) (values hd (Nil (Nat)) (CatNil (Nat) xs) (LNil (Nat))))))))
        ((Cons a2 z rest2)
          (match erased l _
            ((LCons b1 x1 r1 n1 p1)
              (match erased p1 _
                ((LCons b2 x2 r2 n2 p2)
                  (let (many y) (many inner) (erased q) (erased li) (unsnoc tl n2 p1))
                  (values y (Cons (Nat) hd inner)
                          (CatCons (Nat) hd inner (Cons (Nat) y (Nil (Nat))) tl q)
                          (LCons (Nat) hd inner n2 li)))))))))))

(def-fns _ $ many pal-dec : (subterm erased (Nat) len) (many (List (Nat)) w)
    (erased (Length (Nat) w len) l) ->
    (many (Or (Palindrome (Nat) w) (NotPalindrome w)) d)
  (match many w _
    ((Nil a) (InL _ _ (PalNil (Nat))))
    ((Cons a x rest)
      (match many rest _
        ((Nil a2) (InL _ _ (PalOne (Nat) x)))
        ((Cons a2 z rest2)
          (match erased l _
            ((LCons b1 x1 r1 n1 p1)
              (match erased p1 _
                ((LCons b2 x2 r2 n2 p2)
                  (let (many y) (many inner) (erased q) (erased li) (unsnoc rest n2 p1))
                  (let (erased ltp) (lt-weaken n2 (Succ n2) (lt-succ n2)))
                  (match many (nat-cmp x y) _
                    ((CEq t r x0)
                      (match many (pal-dec (subterm (lt-subterm n2 len ltp)) n2 inner li) _
                        ((InL s0 s1 p0) (InL _ _ (PalWrap (Nat) x inner rest p0 q)))
                        ((InR s0 s1 np0) (InR _ _ (NotPalInner x inner rest q np0)))))
                    ((CLt t r a0 b0 p0)
                      (InR _ _ (NotPalEnds x y inner rest q (ApartLt x y p0))))
                    ((CGt t r a0 b0 p0)
                      (InR _ _ (NotPalEnds x y inner rest q (ApartGt x y p0))))))))))))))

(def-fns _ $ many has-dec : (subterm many (List (Nat)) xs) (many (Nat) n) ->
    (many (Or (HasPalindromeOfLength xs n) (NoPalindromeOfLengthF xs n)) d)
  (match many (take-dec n xs) _
    ((TakeNo n0 xs0 len l short) (InR _ _ (SlideShort xs n len l short)))
    ((TakeYes n0 xs0 w tk)
      (let (many wlen) (erased wl) (list-length w))
      (match many (pal-dec wlen w wl) _
        ((InL s0 s1 p0) (InL _ _ (HasHere xs n w tk p0)))
        ((InR s0 s1 np0)
          (match many xs _
            ((Nil a) (match erased tk _ ((TakeZero b1 xs1) (match erased np0 _))))
            ((Cons a hd tl)
              (match many (has-dec tl n) _
                ((InL t0 t1 h) (InL _ _ (HasThere hd tl n h)))
                ((InR t0 t1 np) (InR _ _ (SlideStep n hd tl w tk np0 np)))))))))))

(def-fns _ $ many longest-down : (many (List (Nat)) xs) (subterm many (Nat) k)
    (erased (NoLargerPalindromeF xs k) nl) ->
    (many (Nat) n) (erased (LongestPalindromeF xs n) p)
  (match many k _
    ((Zero)
      (values k (IsLongestF xs k
                  (HasHere xs k (Nil (Nat)) (TakeZero (Nat) xs) (PalNil (Nat))) nl)))
    ((Succ j)
      (match many (has-dec xs k) _
        ((InL t0 t1 h) (values k (IsLongestF xs k h nl)))
        ((InR t0 t1 np) (longest-down xs j (NoLargerStepF xs j np nl)))))))

(def-fns _ $ many longest-fused : (many (List (Nat)) xs) ->
    (many (Nat) n) (erased (LongestPalindromeF xs n) p)
  (let (many len) (erased l) (list-length xs))
  (longest-down xs len (NoLargerDoneF xs len len l (lt-succ len))))

(def-fns _ $ erased take-short-absurd : (erased (Nat) n) (erased (List (Nat)) xs)
    (erased (List (Nat)) w) (subterm erased (Take (Nat) n xs w) tk)
    (erased (Nat) len) (erased (Length (Nat) xs len) l) (erased (Lt len n) short) ->
    (erased (False) f)
  (match erased tk _
    ((TakeZero b1 xs1) (match erased short _))
    ((TakeSucc b1 n1 x1 xs1 w1 t1)
      (match erased l _
        ((LCons b2 x2 r2 len2 l2)
          (match erased short _
            ((LtS a3 b3 s3) (take-short-absurd n1 xs1 w1 t1 len2 l2 s3))))))))

(def-fns _ $ erased has-short-absurd : (erased (List (Nat)) xs) (erased (Nat) n)
    (subterm erased (HasPalindromeOfLength xs n) h)
    (erased (Nat) len) (erased (Length (Nat) xs len) l) (erased (Lt len n) short) ->
    (erased (False) f)
  (match erased h _
    ((HasHere xs1 n1 w1 tk1 p1) (take-short-absurd n xs w1 tk1 len l short))
    ((HasThere x1 xs1 n1 h1)
      (match erased l _
        ((LCons b2 x2 r2 len2 l2)
          (has-short-absurd xs1 n h1 len2 l2
            (lt-trans len2 (Succ len2) n (lt-succ len2) short)))))))

(def-fns _ $ erased windows-total : (erased (Nat) n) (subterm erased (List (Nat)) xs) ->
    (erased (List (List (Nat))) xss) (erased (Windows (Nat) n xs xss) w)
  (match erased xs _
    ((Nil a)
      (match erased n _
        ((Zero) (values (Cons (List (Nat)) (Nil (Nat)) (Nil (List (Nat)))) (WinEmpty (Nat))))
        ((Succ k)
          (values (Nil (List (Nat))) (WinStop (Nat) n xs (Zero) (LNil (Nat)) (LtZ k))))))
    ((Cons a hd tl)
      (match erased (take-dec n xs) _
        ((TakeYes n0 xs0 w0 tk0)
          (let (erased xss1) (erased r1) (windows-total n tl))
          (values (Cons (List (Nat)) w0 xss1) (WinStep (Nat) n hd tl w0 tk0 xss1 r1)))
        ((TakeNo n0 xs0 len l short)
          (values (Nil (List (Nat))) (WinStop (Nat) n xs len l short)))))))

(def-fns _ $ erased has-windows : (erased (List (Nat)) xs) (erased (Nat) n)
    (subterm erased (HasPalindromeOfLength xs n) h) ->
    (erased (List (List (Nat))) xss) (erased (Windows (Nat) n xs xss) w)
    (erased (Exists (List (Nat)) NatPalindrome xss) e)
  (match erased h _
    ((HasHere xs1 n1 w1 tk1 p1)
      (match erased xs _
        ((Nil a)
          (match erased tk1 _
            ((TakeZero b1 xs2)
              (values (Cons (List (Nat)) (Nil (Nat)) (Nil (List (Nat))))
                      (WinEmpty (Nat))
                      (ExHere (List (Nat)) NatPalindrome (Nil (Nat)) (Nil (List (Nat)))
                              (IsNatPalindrome (Nil (Nat)) p1))))))
        ((Cons a hd tl)
          (let (erased xss1) (erased r1) (windows-total n tl))
          (values (Cons (List (Nat)) w1 xss1)
                  (WinStep (Nat) n hd tl w1 tk1 xss1 r1)
                  (ExHere (List (Nat)) NatPalindrome w1 xss1 (IsNatPalindrome w1 p1))))))
    ((HasThere x1 xs1 n1 h1)
      (let (erased xss1) (erased r1) (erased e1) (has-windows xs1 n h1))
      (match erased (take-dec n xs) _
        ((TakeYes n0 xs0 w0 tk0)
          (values (Cons (List (Nat)) w0 xss1)
                  (WinStep (Nat) n x1 xs1 w0 tk0 xss1 r1)
                  (ExThere (List (Nat)) NatPalindrome w0 xss1 e1)))
        (absurd (TakeNo n0 xs0 len l short) (has-short-absurd xs n h len l short))))))

(def-fns _ $ erased nopal-parts : (erased (List (Nat)) xs) (erased (Nat) n)
    (subterm erased (NoPalindromeOfLengthF xs n) np) ->
    (erased (List (List (Nat))) xss) (erased (Windows (Nat) n xs xss) w)
    (erased (All (List (Nat)) NotPalindrome xss) a)
  (match erased np _
    ((SlideShort xs1 n1 len l short)
      (values (Nil (List (Nat)))
              (WinStop (Nat) n xs len l short)
              (AllNil (List (Nat)) NotPalindrome)))
    ((SlideStep n1 x1 xs1 w1 tk1 npw rest)
      (let (erased xss1) (erased r1) (erased a1) (nopal-parts xs1 n rest))
      (values (Cons (List (Nat)) w1 xss1)
              (WinStep (Nat) n x1 xs1 w1 tk1 xss1 r1)
              (AllCons (List (Nat)) NotPalindrome w1 xss1 npw a1)))))

(def-fns _ $ erased nolarger-spec : (erased (List (Nat)) xs) (erased (Nat) n)
    (subterm erased (NoLargerPalindromeF xs n) nl) -> (erased (NoLargerPalindrome xs n) r)
  (match erased nl _
    ((NoLargerDoneF xs1 n1 len l short) (NoLargerDone xs n len l short))
    ((NoLargerStepF xs1 n1 here rest)
      (let (erased xss) (erased w) (erased a) (nopal-parts xs (Succ n) here))
      (NoLargerStep xs n (NoPal xs (Succ n) xss w a) (nolarger-spec xs (Succ n) rest)))))

(def-fns _ $ many longest : (many (List (Nat)) xs) ->
    (many (Nat) n) (erased (LongestPalindrome xs n) p)
  (let (many n) (erased pf) (longest-fused xs))
  (match erased pf (((Nat) rn) ((LongestPalindrome xs rn) rp))
    ((IsLongestF xs1 n1 h nl)
      (let (erased xss) (erased w) (erased e) (has-windows xs n h))
      (values n (IsLongest xs n xss w e (nolarger-spec xs n nl))))))

(def-fns _ $ many lp : (many (List (Nat)) xs) -> (many (Nat) n)
  (let (many n) (erased p) (longest xs))
  n)

(Cons (Nat) (lp (Nil (Nat)))
  $ Cons (Nat) (lp $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Nil (Nat))
  $ Cons (Nat) (lp $ Cons (Nat) 1 $ Cons (Nat) 2 $ Cons (Nat) 3 $ Cons (Nat) 2 $ Cons (Nat) 5 $ Nil (Nat))
  $ Cons (Nat) (lp $ Cons (Nat) 9 $ Cons (Nat) 4 $ Cons (Nat) 5 $ Cons (Nat) 5 $ Cons (Nat) 4 $ Cons (Nat) 8 $ Nil (Nat))
  $ Cons (Nat) (lp $ Cons (Nat) 7 $ Cons (Nat) 7 $ Cons (Nat) 7 $ Nil (Nat))
  $ Nil (Nat))
