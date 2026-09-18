; Center certificates and their bridge to the original substring relation.
; All functions in this file are erased. Runtime algorithms need only carry
; their radii and the proofs of the comparisons they actually perform.

(def-adts
  (PalLcp : ((List (Nat)) left right) ((Nat) n) -> Type enum
    (many PLLeft : (erased (List (Nat)) right) -> (PalLcp (Nil (Nat)) right (Zero)))
    (many PLRight : (erased (List (Nat)) left) -> (PalLcp left (Nil (Nat)) (Zero)))
    (many PLApart : (erased (Nat) x y) (erased (List (Nat)) left right)
      (erased (NatApart x y) apart) ->
      (PalLcp (Cons (Nat) x left) (Cons (Nat) y right) (Zero)))
    (many PLStep : (erased (Nat) x) (erased (List (Nat)) left right)
      (erased (Nat) n) (erased (PalLcp left right n) p) ->
      (PalLcp (Cons (Nat) x left) (Cons (Nat) x right) (Succ n))))
  (PalSplit : ((List (Nat)) xs left right) -> Type enum
    (many PSStart : (erased (List (Nat)) xs) -> (PalSplit xs (Nil (Nat)) xs))
    (many PSStep : (erased (List (Nat)) xs left right) (erased (Nat) x)
      (erased (PalSplit xs left (Cons (Nat) x right)) p) ->
      (PalSplit xs (Cons (Nat) x left) right))))

(def-fns _ $ erased fp-split-has : (erased (List (Nat)) xs left right)
    (erased (Nat) n) (subterm erased (PalSplit xs left right) split)
    (erased (HasPalindromeOfLength right n) has) ->
    (erased (HasPalindromeOfLength xs n) out)
  (match erased split _
    ((PSStart source) has)
    ((PSStep source l r x p)
      (fp-split-has xs l (Cons (Nat) x right) n p (HasThere x right n has)))))

(def-fns _ $ erased fp-center-base : (erased (List (Nat)) xs left right mid full)
    (erased (Nat) m n) (erased (PalSplit xs left full) split)
    (erased (Palindrome (Nat) mid) pal) (erased (Length (Nat) mid m) len)
    (erased (Concat (Nat) mid right full) cat) (erased (Add (Zero) m n) sum) ->
    (erased (HasPalindromeOfLength xs n) has)
  (match erased sum _
    ((AddZero v)
      (fp-split-has xs left full n split
        (HasHere full n mid (fp-take-concat (Nat) mid right full n cat len) pal)))))

; Wrap the middle in each matched pair, moving backwards through the split.
(def-fns _ $ erased fp-center-witness : (erased (List (Nat)) xs left right)
    (erased (Nat) k d) (subterm erased (PalLcp left right k) common)
    (erased (Double k d) twice)
    (erased (List (Nat)) mid full) (erased (Nat) m n)
    (erased (PalSplit xs left full) split) (erased (Palindrome (Nat) mid) pal)
    (erased (Length (Nat) mid m) len) (erased (Concat (Nat) mid right full) cat)
    (erased (Add d m n) sum) -> (erased (HasPalindromeOfLength xs n) has)
  (match erased common _
    ((PLLeft r)
      (match erased twice _
        ((D0) (fp-center-base xs left right mid full m n split pal len cat sum))))
    ((PLRight l)
      (match erased twice _
        ((D0) (fp-center-base xs left right mid full m n split pal len cat sum))))
    ((PLApart x y l r apart)
      (match erased twice _
        ((D0) (fp-center-base xs left right mid full m n split pal len cat sum))))
    ((PLStep x l r k1 p)
      (match erased split _
        ((PSStep source l2 full2 y split1)
          (match erased twice _
            ((DS k2 d1 twice1)
              (match erased sum _
                ((AddSucc a b c sum1)
                  (match erased sum1 _
                    ((AddSucc a2 b2 c2 sum2)
                      (let (erased withx) (erased snoc) (erased restcat)
                        (fp-concat-unassoc (Nat) mid (Cons (Nat) x (Nil (Nat))) r
                          right full cat
                          (CatCons (Nat) x (Nil (Nat)) r r (CatNil (Nat) r))))
                      (let (erased withxlen)
                        (fp-concat-length (Nat) mid (Cons (Nat) x (Nil (Nat))) withx
                          m (Succ (Zero)) (Succ m) snoc len
                          (LCons (Nat) x (Nil (Nat)) (Zero) (LNil (Nat)))
                          (add-succ-right m (Zero) m (add-zero-right m))))
                      (fp-center-witness xs l r k1 d1 p twice1
                        (Cons (Nat) x withx) (Cons (Nat) x full) (Succ (Succ m)) n
                        split1 (PalWrap (Nat) x mid withx pal snoc)
                        (LCons (Nat) x withx (Succ m) withxlen)
                        (CatCons (Nat) x withx r full restcat)
                        (add-succ-right d1 (Succ m) (Succ c2)
                          (add-succ-right d1 m c2 sum2))))))))))))))

(def-fns _ $ erased fp-apart-irrefl : (erased (Nat) x)
    (erased (NatApart x x) p) -> (erased (False) f)
  (match erased p _
    ((ApartLt a b lt) (lt-asym x x lt (lt-succ x)))
    ((ApartGt a b gt) (lt-asym x x gt (lt-succ x)))))

(def-fns _ $ erased fp-lcp-lower : (erased (List (Nat)) left right)
    (erased (Nat) radius k) (subterm erased (List (Nat)) w)
    (erased (PalLcp left right radius) common)
    (erased (Take (Nat) k left w) tl) (erased (Take (Nat) k right w) tr)
    (erased (Length (Nat) w k) len) -> (erased (Lt k (Succ radius)) bound)
  (match erased w _
    ((Nil a) (match erased len _ ((LNil b) (LtZ radius))))
    ((Cons a x rest)
      (match erased len _
        ((LCons b y rest2 k1 len1)
          (match erased tl _
            ((TakeSucc c j z ls ws tl1)
              (match erased tr _
                ((TakeSucc d j2 z2 rs ws2 tr1)
                  (match erased common _
                    (absurd (PLApart u v l r apart) (fp-apart-irrefl x apart))
                    ((PLStep u l r radius1 p)
                      (LtS k1 (Succ radius1)
                        (fp-lcp-lower ls rs radius1 k1 rest p tl1 tr1 len1)))))))))))))

(def-fns _ $ erased fp-double-mono : (erased (Nat) a aa b bb)
    (subterm erased (Double a aa) pa) (erased (Double b bb) pb)
    (erased (Lt a (Succ b)) bound) -> (erased (Lt aa (Succ bb)) out)
  (match erased pa _
    ((D0) (LtZ bb))
    ((DS a1 aa1 pa1)
      (match erased pb _
        (absurd (D0)
          (match erased bound (((False) f)) ((LtS x y p) (match erased p _))))
        ((DS b1 bb1 pb1)
          (match erased bound _
            ((LtS x y p)
              (LtS (Succ aa1) (Succ (Succ bb1))
                (LtS aa1 (Succ bb1) (fp-double-mono a1 aa1 b1 bb1 pa1 pb1 p))))))))))

(def-fns _ $ erased fp-le-trans : (erased (Nat) a b c)
    (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) ->
    (erased (Lt a (Succ c)) r)
  (lt-le-trans a (Succ b) (Succ c) p (LtS b (Succ c) q)))

(def-adts $ PalCenterBounds : ((List (Nat)) left right) ((Nat) n) -> Type
  enum
  (many PCBEnd : (erased (List (Nat)) left) (erased (Nat) n) ->
    (PalCenterBounds left (Nil (Nat)) n))
  (many PCBStep : (erased (List (Nat)) left right) (erased (Nat) x n e o de do)
    (erased (PalLcp left (Cons (Nat) x right) e) even)
    (erased (PalLcp left right o) odd)
    (erased (Double e de) twicee) (erased (Double o do) twiceo)
    (erased (Lt de (Succ n)) be) (erased (Lt (Succ do) (Succ n)) bo)
    (erased (PalCenterBounds (Cons (Nat) x left) right n) rest) ->
    (PalCenterBounds left (Cons (Nat) x right) n)))

(def-fns _ $ erased fp-bounds-weaken : (erased (List (Nat)) left right)
    (erased (Nat) n m) (subterm erased (PalCenterBounds left right n) bounds)
    (erased (Lt n (Succ m)) le) -> (erased (PalCenterBounds left right m) out)
  (match erased bounds _
    ((PCBEnd l k) (PCBEnd left m))
    ((PCBStep l r x k e o de do even odd twicee twiceo be bo rest)
      (PCBStep left r x m e o de do even odd twicee twiceo
        (fp-le-trans de n m be le) (fp-le-trans (Succ do) n m bo le)
        (fp-bounds-weaken (Cons (Nat) x left) r n m rest le)))))

(def-fns _ $ erased fp-bounds-even : (erased (List (Nat)) left right)
    (erased (Nat) n) (erased (PalCenterBounds left right n) bounds) ->
    (erased (Nat) e de) (erased (PalLcp left right e) common)
    (erased (Double e de) twice) (erased (Lt de (Succ n)) bound)
  (match erased bounds _
    ((PCBEnd l k) (values (Zero) (Zero) (PLRight left) (D0) (LtZ n)))
    ((PCBStep l r x k e o de do even odd twicee twiceo be bo rest)
      (values e de even twicee be))))

(def-fns _ $ erased fp-add-shift : (erased (Nat) a b c)
    (subterm erased (Add a (Succ b) c) p) ->
    (erased (Add (Succ a) b c) q)
  (match erased p _
    ((AddZero v) (AddSucc (Zero) b b (AddZero b)))
    ((AddSucc x y z p1) (AddSucc (Succ x) b z (fp-add-shift x b z p1)))))

; Follow a palindrome towards its center. The peeled characters form the
; common prefix of the reversed left context and the right context there.
; Thus its length is bounded by the exact radius certified at that center.
(def-fns _ $ erased fp-pal-prefix-bound :
    (erased (List (Nat)) left right stack tail stacktail w)
    (erased (Nat) k d width total n)
    (erased (Take (Nat) k left stack) takeleft)
    (erased (Length (Nat) stack k) stacklen)
    (erased (Concat (Nat) stack tail stacktail) stackcat)
    (erased (Concat (Nat) w stacktail right) cat)
    (subterm erased (Palindrome (Nat) w) pal)
    (erased (Length (Nat) w width) len)
    (erased (Double k d) twice) (erased (Add d width total) sum)
    (erased (PalCenterBounds left right n) bounds) ->
    (erased (Lt total (Succ n)) out)
  (match erased pal _
    ((PalNil a)
      (match erased len _
        ((LNil b)
          (match erased cat _
            ((CatNil c rest)
              (match erased (fp-add-unique d (Zero) total d sum (add-zero-right d)) _
                ((Refl t v)
                  (let (erased e) (erased de) (erased common) (erased two) (erased bound)
                    (fp-bounds-even left right n bounds))
                  (let (erased le)
                    (fp-lcp-lower left right e k stack common takeleft
                      (fp-take-concat (Nat) stack tail right k stackcat stacklen) stacklen))
                  (fp-le-trans d de n (fp-double-mono k d e de twice two le) bound))))))))
    ((PalOne a x)
      (match erased len _
        ((LCons b y rest j lp)
          (match erased lp _
            ((LNil c)
              (match erased cat _
                ((CatCons c y rest catrest out cat1)
                  (match erased cat1 _
                    ((CatNil e rest2)
                      (match erased bounds _
                        ((PCBStep l r x2 n2 e o de do even odd twoe twoo be bo rem)
                          (let (erased eq)
                            (fp-add-unique d (Succ (Zero)) total (Succ d) sum
                              (add-succ-right d (Zero) d (add-zero-right d))))
                          (match erased eq _
                            ((Refl t v)
                              (let (erased le)
                                (fp-lcp-lower left stacktail o k stack odd takeleft
                                  (fp-take-concat (Nat) stack tail stacktail k stackcat stacklen) stacklen))
                              (fp-le-trans (Succ d) (Succ do) n
                                (LtS d (Succ do) (fp-double-mono k d o do twice twoo le)) bo))))))))))))))
    ((PalWrap a x inner withx innerpal snoc)
      (let (erased ni) (erased li) (pal-length inner))
      (let (erased withlen)
        (fp-concat-length (Nat) inner (Cons (Nat) x (Nil (Nat))) withx
          ni (Succ (Zero)) (Succ ni) snoc li
          (LCons (Nat) x (Nil (Nat)) (Zero) (LNil (Nat)))
          (add-succ-right ni (Zero) ni (add-zero-right ni))))
      (match erased (fp-length-unique (Nat) w width (Succ (Succ ni)) len
                      (LCons (Nat) x withx (Succ ni) withlen)) _
        ((Refl t v)
          (match erased cat _
            ((CatCons b y rest tail1 out cat1)
              (let (erased nexttail) (erased tinycat) (erased innercat)
                (fp-concat-assoc (Nat) inner (Cons (Nat) x (Nil (Nat))) withx
                  stacktail out snoc cat1))
              (match erased tinycat _
                ((CatCons c z empty tail2 out2 tailcat)
                  (match erased tailcat _
                    ((CatNil e tail3)
                      (match erased bounds _
                        ((PCBStep l r x2 n2 e o de do even odd twoe twoo be bo rem)
                          (fp-pal-prefix-bound (Cons (Nat) x left) out
                            (Cons (Nat) x stack) tail (Cons (Nat) x stacktail) inner
                            (Succ k) (Succ (Succ d)) ni total n
                            (TakeSucc (Nat) k x left stack takeleft)
                            (LCons (Nat) x stack k stacklen)
                            (CatCons (Nat) x stack tail stacktail stackcat)
                            innercat innerpal li (DS k d twice)
                            (fp-add-shift (Succ d) ni total
                              (fp-add-shift d (Succ ni) total sum)) rem))))))))))))))

(def-fns _ $ erased fp-take-rest : (erased Type A)
    (erased (Nat) n) (erased (List A) xs w)
    (subterm erased (Take A n xs w) tk) ->
    (erased (List A) rest) (erased (Concat A w rest xs) cat)
  (match erased tk _
    ((TakeZero a source) (values xs (CatNil A xs)))
    ((TakeSucc a k x tail out tk1)
      (let (erased rest) (erased cat) (fp-take-rest A k tail out tk1))
      (values rest (CatCons A x out rest tail cat)))))

; Rule out all windows of a larger length using the center bound.
(def-fns _ $ erased fp-bounded-windows : (erased (List (Nat)) left)
    (subterm erased (List (Nat)) right) (erased (Nat) n k)
    (erased (PalCenterBounds left right n) bounds)
    (erased (Lt n (Succ k)) larger) ->
    (erased (List (List (Nat))) ws)
    (erased (Windows (Nat) (Succ k) right ws) wins)
    (erased (All (List (Nat)) NotPalindrome ws) absent)
  (match erased right _
    ((Nil a)
      (values (Nil (List (Nat)))
        (WinStop (Nat) (Succ k) right (Zero) (LNil (Nat)) (LtZ k))
        (AllNil (List (Nat)) NotPalindrome)))
    ((Cons a x rest)
      (match erased (pal-take (Succ k) right) _
        ((PalShort m source len p short)
          (values (Nil (List (Nat))) (WinStop (Nat) (Succ k) right len p short)
            (AllNil (List (Nat)) NotPalindrome)))
        ((PalTaken m source w tk len)
          (match erased (pal-decide (Succ k) w len) _
            (absurd (PalYes v pal)
              (let (erased tail) (erased cat) (fp-take-rest (Nat) (Succ k) right w tk))
              (lt-asym n (Succ k) larger
                (fp-pal-prefix-bound left right (Nil (Nat)) tail tail w
                  (Zero) (Zero) (Succ k) (Succ k) n
                  (TakeZero (Nat) left) (LNil (Nat)) (CatNil (Nat) tail)
                  cat pal len (D0) (AddZero (Succ k)) bounds)))
            ((PalNo v np)
              (match erased bounds _
                ((PCBStep l r y n2 e o de do even odd twoe twoo be bo rem)
                  (let (erased tailws) (erased tailwins) (erased tailabsent)
                    (fp-bounded-windows (Cons (Nat) x left) rest n k rem larger))
                  (values (Cons (List (Nat)) w tailws)
                    (WinStep (Nat) (Succ k) x rest w tk tailws tailwins)
                    (AllCons (List (Nat)) NotPalindrome w tailws np tailabsent)))))))))))

; Descend from the input length to the answer, constructing the specification's
; explicit chain of excluded lengths. This potentially expensive work erases.
(def-fns _ $ erased fp-bounded-above : (erased (List (Nat)) xs)
    (erased (Nat) answer) (subterm erased (Nat) candidate)
    (erased (PalCenterBounds (Nil (Nat)) xs answer) bounds)
    (erased (Lt answer (Succ candidate)) le)
    (erased (NoLargerPalindrome xs candidate) above) ->
    (erased (NoLargerPalindrome xs answer) out)
  (match erased (nat-cmp answer candidate) _
    ((CEq t r a) above)
    (absurd (CGt t r a b gt) (lt-asym candidate answer gt le))
    ((CLt t r a b lt)
      (match erased candidate _
        (absurd (Zero) (match erased lt (((False) f))))
        ((Succ k)
          (let (erased ws) (erased wins) (erased absent)
            (fp-bounded-windows (Nil (Nat)) xs answer k bounds lt))
          (fp-bounded-above xs answer k bounds lt
            (NoLargerStep xs k (NoPal xs candidate ws wins absent) above)))))))

(def-fns _ $ erased fp-centers-spec : (erased (List (Nat)) xs)
    (erased (Nat) n) (erased (PalCenterBounds (Nil (Nat)) xs n) bounds)
    (erased (HasPalindromeOfLength xs n) has) ->
    (erased (LongestPalindrome xs n) correct)
  (let (erased len) (erased lp) (pal-length xs))
  (fp-spec-answer xs n has
    (fp-bounded-above xs n len bounds (fp-has-bound xs n len has lp)
      (NoLargerDone xs len len lp (lt-succ len)))))

; Erased histories let the runtime loops carry only numeric accumulators.
(def-adts $ PalLcpPrefix : ((List (Nat)) fullleft fullright left right) ((Nat) n) -> Type
  enum
  (many PLPStart : (erased (List (Nat)) left right) ->
    (PalLcpPrefix left right left right (Zero)))
  (many PLPStep : (erased (List (Nat)) fullleft fullright left right) (erased (Nat) x n)
    (erased (PalLcpPrefix fullleft fullright (Cons (Nat) x left) (Cons (Nat) x right) n) p) ->
    (PalLcpPrefix fullleft fullright left right (Succ n))))

(def-fns _ $ erased fp-lcp-prefix-close : (erased (List (Nat)) fl fr left right)
    (erased (Nat) n k total) (subterm erased (PalLcpPrefix fl fr left right n) prefix)
    (erased (PalLcp left right k) suffix) (erased (Add n k total) sum) ->
    (erased (PalLcp fl fr total) out)
  (match erased prefix _
    ((PLPStart l r) (match erased sum _ ((AddZero v) suffix)))
    ((PLPStep fl0 fr0 l r x n1 p)
      (match erased sum _
        ((AddSucc a b c q)
          (fp-lcp-prefix-close fl fr (Cons (Nat) x left) (Cons (Nat) x right)
            n1 (Succ k) total p (PLStep x left right k suffix)
            (add-succ-right n1 k c q)))))))

(def-adts $ PalScanned : ((List (Nat)) xs left right) ((Nat) n) -> Type enum
  (many PSCStart : (erased (List (Nat)) xs) (erased (Nat) n) ->
    (PalScanned xs (Nil (Nat)) xs n))
  (many PSCStep : (erased (List (Nat)) xs left right) (erased (Nat) x n e o de do)
    (erased (PalLcp left (Cons (Nat) x right) e) even)
    (erased (PalLcp left right o) odd)
    (erased (Double e de) twicee) (erased (Double o do) twiceo)
    (erased (Lt de (Succ n)) be) (erased (Lt (Succ do) (Succ n)) bo)
    (erased (PalScanned xs left (Cons (Nat) x right) n) previous) ->
    (PalScanned xs (Cons (Nat) x left) right n)))

(def-fns _ $ erased fp-scanned-weaken : (erased (List (Nat)) xs left right)
    (erased (Nat) n m) (subterm erased (PalScanned xs left right n) scanned)
    (erased (Lt n (Succ m)) le) -> (erased (PalScanned xs left right m) out)
  (match erased scanned _
    ((PSCStart source old) (PSCStart xs m))
    ((PSCStep source l r x old e o de do even odd twicee twiceo be bo previous)
      (PSCStep xs l r x m e o de do even odd twicee twiceo
        (fp-le-trans de n m be le) (fp-le-trans (Succ do) n m bo le)
        (fp-scanned-weaken xs l (Cons (Nat) x r) n m previous le)))))

(def-fns _ $ erased fp-scanned-close : (erased (List (Nat)) xs left right)
    (erased (Nat) n) (subterm erased (PalScanned xs left right n) scanned)
    (erased (PalCenterBounds left right n) remaining) ->
    (erased (PalCenterBounds (Nil (Nat)) xs n) all)
  (match erased scanned _
    ((PSCStart source bound) remaining)
    ((PSCStep source l r x bound e o de do even odd twicee twiceo be bo previous)
      (fp-scanned-close xs l (Cons (Nat) x r) n previous
        (PCBStep l r x n e o de do even odd twicee twiceo be bo remaining)))))
