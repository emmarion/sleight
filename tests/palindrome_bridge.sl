; needs: palindrome_relations
; Shared by longest_palindrome.sl and manacher.sl: a Take decider, the length and functionality of
; Take, and the bridge from the fused PART 2 relations of palindrome_relations.sl to its PART 1 spec
; (the proof plan's B1-B5). Written by a Claude session; the checker is the evidence.

(def-fns _ $ many list-length : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n) (erased (Length A xs n) l)
  (match many xs _
    ((Nil a) (values (Zero) (LNil A)))
    ((Cons a x rest)
      (let (many n) (erased l) (list-length A rest))
      (values (Succ n) (LCons A x rest n l)))))

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

