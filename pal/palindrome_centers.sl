; Center certificates and their bridge to the original substring relation.
; All functions in this file are erased. Runtime algorithms need only carry
; their radii and the proofs of the comparisons they actually perform.

(def-adts
  ((PalLcp : ((List (Nat)) left right) ((Nat) n) -> Type) enum
    (many PLLeft : (erased (List (Nat)) right) -> (PalLcp (Nil (Nat)) right (Zero)))
    (many PLRight : (erased (List (Nat)) left) -> (PalLcp left (Nil (Nat)) (Zero)))
    (many PLApart : (erased (Nat) x y) (erased (List (Nat)) left right)
      (erased (NatApart x y) apart)
      -> (PalLcp (Cons (Nat) x left) (Cons (Nat) y right) (Zero)))
    (many PLStep : (erased (Nat) x) (erased (List (Nat)) left right)
      (erased (Nat) n) (erased (PalLcp left right n) p)
      -> (PalLcp (Cons (Nat) x left) (Cons (Nat) x right) (Succ n))))
  ((PalSplit : ((List (Nat)) xs left right) -> Type) enum
    (many PSStart : (erased (List (Nat)) xs) -> (PalSplit xs (Nil (Nat)) xs))
    (many PSStep : (erased (List (Nat)) xs left right) (erased (Nat) x)
      (erased (PalSplit xs left (Cons (Nat) x right)) p)
      -> (PalSplit xs (Cons (Nat) x left) right))))

(def-fns _ $ (erased fp-split-has : (erased (List (Nat)) xs left right)
    (erased (Nat) n) (subterm erased (PalSplit xs left right) split)
    (erased (HasPalindromeOfLength right n) has) ->
    (erased (HasPalindromeOfLength xs n) out))
  (match erased split _
    ((PSStart source) has)
    ((PSStep source l r x p)
      (fp-split-has xs l _ n p (HasThere x _ _ has)))))

(def-fns _ $ (erased fp-center-base : (erased (List (Nat)) xs left right mid full)
    (erased (Nat) m n) (erased (PalSplit xs left full) split)
    (erased (Palindrome (Nat) mid) pal) (erased (PalLength (Nat) mid m) len)
    (erased (PalConcat (Nat) mid right full) cat) (erased (Add (Zero) m n) sum) ->
    (erased (HasPalindromeOfLength xs n) has))
  (let-match erased sum (AddZero v))
  (fp-split-has xs left full n split
    (HasHere _ n _ (fp-take-concat _ mid right full n cat len) pal)))

; Wrap the middle in each matched pair, moving backwards through the split.
(def-fns _ $ (erased fp-center-witness : (erased (List (Nat)) xs left right)
    (erased (Nat) k d) (subterm erased (PalLcp left right k) common)
    (erased (Double k d) twice)
    (erased (List (Nat)) mid full) (erased (Nat) m n)
    (erased (PalSplit xs left full) split) (erased (Palindrome (Nat) mid) pal)
    (erased (PalLength (Nat) mid m) len) (erased (PalConcat (Nat) mid right full) cat)
    (erased (Add d m n) sum) -> (erased (HasPalindromeOfLength xs n) has))
  (match erased common _
    ((PLLeft r)
      (let-match erased twice (D0))
      (fp-center-base xs left right mid full m n split pal len cat sum))
    ((PLRight l)
      (let-match erased twice (D0))
      (fp-center-base xs left right mid full m n split pal len cat sum))
    ((PLApart x y l r apart)
      (let-match erased twice (D0))
      (fp-center-base xs left right mid full m n split pal len cat sum))
    ((PLStep x l r k1 p)
      (let-match erased split (PSStep source l2 full2 y split1))
      (let-match erased twice (DS k2 d1 twice1))
      (let-match erased sum (AddSucc a b c sum1))
      (let-match erased sum1 (AddSucc a2 b2 c2 sum2))
      (let ((erased withx) (erased snoc) (erased restcat))
        (fp-concat-unassoc _ mid _ r
          right full cat
          (PalCatCons _ x _ _ _ (PalCatNil _ r))))
      (let ((erased withxlen))
        (fp-concat-length _ mid _ withx
          m (Succ (Zero)) _ snoc len
          (PalLCons _ x _ _ (PalLNil _))
          (add-succ-right m (Zero) m (add-zero-right m))))
      (fp-center-witness xs l r k1 d1 p twice1
        (Cons _ x withx) (Cons _ x full) (Succ (Succ m)) n
        split1 (PalWrap _ x _ _ pal snoc)
        (PalLCons _ x _ _ withxlen)
        (PalCatCons _ x _ _ _ restcat)
        (add-succ-right d1 _ _
          (add-succ-right d1 m c2 sum2))))))

(def-fns _ $ (erased absurd fp-apart-irrefl : (erased (Nat) x)
    (erased (NatApart x x) p) -> (erased (False) f))
  (match erased p _
    (absurd (ApartLt a b lt) (lt-asym x x lt (lt-succ x)))
    (absurd (ApartGt a b gt) (lt-asym x x gt (lt-succ x)))))

(def-fns _ $ (erased fp-lcp-lower : (erased (List (Nat)) left right)
    (erased (Nat) radius k) (subterm erased (List (Nat)) w)
    (erased (PalLcp left right radius) common)
    (erased (Take (Nat) k left w) tl) (erased (Take (Nat) k right w) tr)
    (erased (PalLength (Nat) w k) len) -> (erased (Lt k (Succ radius)) bound))
  (match erased w _
    ((Nil a)
      (let-match erased len (PalLNil b))
      (LtZ radius))
    ((Cons a x rest)
      (let-match erased len (PalLCons b y rest2 k1 len1))
      (let-match erased tl (TakeSucc c j z ls ws tl1))
      (let-match erased tr (TakeSucc d j2 z2 rs ws2 tr1))
      (match erased common _
        (absurd (PLApart u v l r apart) (fp-apart-irrefl x apart))
        ((PLStep u l r radius1 p)
          (LtS _ _
            (fp-lcp-lower ls rs radius1 k1 rest p tl1 tr1 len1)))))))

(def-fns _ $ (erased fp-double-mono : (erased (Nat) a aa b bb)
    (subterm erased (Double a aa) pa) (erased (Double b bb) pb)
    (erased (Lt a (Succ b)) bound) -> (erased (Lt aa (Succ bb)) out))
  (match erased pa _
    ((D0) (LtZ bb))
    ((DS a1 aa1 pa1)
      (match erased pb _
        (absurd (D0)
          (let-match erased bound (LtS x y p)) p)
        ((DS b1 bb1 pb1)
          (let-match erased bound (LtS x y p))
          (LtS _ _
            (LtS _ _ (fp-double-mono a1 aa1 b1 bb1 pa1 pb1 p))))))))

(def-fns _ $ (erased fp-le-trans : (erased (Nat) a b c)
    (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) ->
    (erased (Lt a (Succ c)) r))
  (lt-le-trans a _ _ p (LtS _ _ q)))

(def-adts $ (PalCenterBounds : ((List (Nat)) left right) ((Nat) n) -> Type)
  enum
  (many PCBEnd : (erased (List (Nat)) left) (erased (Nat) n)
    -> (PalCenterBounds left (Nil (Nat)) n))
  (many PCBStep : (erased (List (Nat)) left right) (erased (Nat) x n e o de do)
    (erased (PalLcp left (Cons (Nat) x right) e) even)
    (erased (PalLcp left right o) odd)
    (erased (Double e de) twicee) (erased (Double o do) twiceo)
    (erased (Lt de (Succ n)) be) (erased (Lt (Succ do) (Succ n)) bo)
    (erased (PalCenterBounds (Cons (Nat) x left) right n) rest)
    -> (PalCenterBounds left (Cons (Nat) x right) n)))

(def-fns _ $ (erased fp-bounds-weaken : (erased (List (Nat)) left right)
    (erased (Nat) n m) (subterm erased (PalCenterBounds left right n) bounds)
    (erased (Lt n (Succ m)) le) -> (erased (PalCenterBounds left right m) out))
  (match erased bounds _
    ((PCBEnd l k) (PCBEnd left m))
    ((PCBStep l r x k e o de do even odd twicee twiceo be bo rest)
      (PCBStep left r x m e o de do even odd twicee twiceo
        (fp-le-trans de n m be le) (fp-le-trans _ n m bo le)
        (fp-bounds-weaken _ r n m rest le)))))

(def-fns _ $ (erased fp-bounds-even : (erased (List (Nat)) left right)
    (erased (Nat) n) (erased (PalCenterBounds left right n) bounds) ->
    (erased (Nat) e de) (erased (PalLcp left right e) common)
    (erased (Double e de) twice) (erased (Lt de (Succ n)) bound))
  (match erased bounds _
    ((PCBEnd l k) (values (Zero) (Zero) (PLRight left) (D0) (LtZ n)))
    ((PCBStep l r x k e o de do even odd twicee twiceo be bo rest)
      (values e de even twicee be))))

(def-fns _ $ (erased fp-add-shift : (erased (Nat) a b c)
    (subterm erased (Add a (Succ b) c) p) ->
    (erased (Add (Succ a) b c) q))
  (match erased p _
    ((AddZero v) (AddSucc _ _ _ (AddZero b)))
    ((AddSucc x y z p1) (AddSucc _ _ _ (fp-add-shift x b z p1)))))

; Follow a palindrome towards its center. The peeled characters form the
; common prefix of the reversed left context and the right context there.
; Thus its length is bounded by the exact radius certified at that center.
(def-fns _ $ (erased fp-pal-prefix-bound :
    (erased (List (Nat)) left right stack tl2 stacktail w)
    (erased (Nat) k d width total n)
    (erased (Take (Nat) k left stack) takeleft)
    (erased (PalLength (Nat) stack k) stacklen)
    (erased (PalConcat (Nat) stack tl2 stacktail) stackcat)
    (erased (PalConcat (Nat) w stacktail right) cat)
    (subterm erased (Palindrome (Nat) w) pal)
    (erased (PalLength (Nat) w width) len)
    (erased (Double k d) twice) (erased (Add d width total) sum)
    (erased (PalCenterBounds left right n) bounds) ->
    (erased (Lt total (Succ n)) out))
  (match erased pal _
    ((PalNil a)
      (let-match erased len (PalLNil b))
      (let-match erased cat (PalCatNil c rest))
      (let-match erased (fp-add-unique d (Zero) total d sum (add-zero-right d)) (Refl t v))
      (let ((erased e) (erased de) (erased common) (erased two) (erased bound))
        (fp-bounds-even left right n bounds))
      (let ((erased le))
        (fp-lcp-lower left right e k stack common takeleft
          (fp-take-concat _ stack tl2 right k stackcat stacklen) stacklen))
      (fp-le-trans d de n (fp-double-mono k d e de twice two le) bound))
    ((PalOne a x)
      (let-match erased len (PalLCons b y rest j lp))
      (let-match erased lp (PalLNil c))
      (let-match erased cat (PalCatCons c3 y2 rest3 catrest out cat1))
      (let-match erased cat1 (PalCatNil e rest2))
      (let-match erased bounds (PCBStep l r x2 n2 e2 o de do even odd twoe twoo be bo rem))
      (let ((erased eq))
        (fp-add-unique d (Succ (Zero)) total _ sum
          (add-succ-right d (Zero) d (add-zero-right d))))
      (let-match erased eq (Refl t v))
      (let ((erased le))
        (fp-lcp-lower left stacktail o k stack odd takeleft
          (fp-take-concat _ stack tl2 stacktail k stackcat stacklen) stacklen))
      (fp-le-trans _ _ n
        (LtS _ _ (fp-double-mono k d o do twice twoo le)) bo))
    ((PalWrap a x inner withx innerpal snoc)
      (let ((erased ni) (erased li)) (pal-length inner))
      (let ((erased withlen))
        (fp-concat-length _ inner _ withx
          ni (Succ (Zero)) _ snoc li
          (PalLCons _ x _ _ (PalLNil _))
          (add-succ-right ni (Zero) ni (add-zero-right ni))))
      (let-match erased (fp-length-unique _ w width _ len
                      (PalLCons _ x _ _ withlen)) (Refl t v))
      (let-match erased cat (PalCatCons b y rest tail1 out cat1))
      (let ((erased nexttail) (erased tinycat) (erased innercat))
        (fp-concat-assoc _ inner _ withx
          stacktail out snoc cat1))
      (let-match erased tinycat (PalCatCons c z empty tail2 out2 tailcat))
      (let-match erased tailcat (PalCatNil e tail3))
      (let-match erased bounds (PCBStep l r x2 n2 e2 o de do even odd twoe twoo be bo rem))
      (fp-pal-prefix-bound _ out
        _ tl2 _ inner
        _ _ ni total n
        (TakeSucc _ _ x _ _ takeleft)
        (PalLCons _ x _ _ stacklen)
        (PalCatCons _ x _ _ _ stackcat)
        innercat innerpal li (DS _ _ twice)
        (fp-add-shift _ ni total
          (fp-add-shift d _ total sum)) rem))))

(def-fns _ $ (erased fp-take-rest : (erased Type A)
    (erased (Nat) n) (erased (List A) xs w)
    (subterm erased (Take A n xs w) tk) ->
    (erased (List A) rest) (erased (PalConcat A w rest xs) cat))
  (match erased tk _
    ((TakeZero a source) (values xs (PalCatNil _ xs)))
    ((TakeSucc a k x tail4 out tk1)
      (let ((erased rest) (erased cat)) (fp-take-rest _ k tail4 out tk1))
      (values rest (PalCatCons _ x _ _ _ cat)))))

; Rule out all windows of a larger length using the center bound.
(def-fns _ $ (erased fp-bounded-windows : (erased (List (Nat)) left)
    (subterm erased (List (Nat)) right) (erased (Nat) n k)
    (erased (PalCenterBounds left right n) bounds)
    (erased (Lt n (Succ k)) larger) ->
    (erased (List (List (Nat))) ws)
    (erased (Windows (Nat) (Succ k) right ws) wins)
    (erased (All (List (Nat)) NotPalindrome ws) absent))
  (match erased right _
    ((Nil a)
      (values (Nil _)
        (WinStop _ _ right (Zero) (PalLNil _) (LtZ k))
        (AllNil _ NotPalindrome)))
    ((Cons a x rest)
      (match erased (pal-take (Succ k) right) _
        ((PalShort m source len p short)
          (values (Nil _) (WinStop _ _ right len p short)
            (AllNil _ NotPalindrome)))
        ((PalTaken m source w tk len)
          (match erased (pal-decide _ w len) _
            (absurd (PalYes v pal)
              (let ((erased tail4) (erased cat)) (fp-take-rest _ _ right w tk))
              (lt-asym n _ larger
                (fp-pal-prefix-bound left right (Nil _) tail4 tail4 w
                  (Zero) (Zero) _ _ n
                  (TakeZero _ left) (PalLNil _) (PalCatNil _ tail4)
                  cat pal len (D0) (AddZero _) bounds)))
            ((PalNo v np)
              (let-match erased bounds (PCBStep l r y n2 e o de do even odd twoe twoo be bo rem))
              (let ((erased tailws) (erased tailwins) (erased tailabsent))
                (fp-bounded-windows _ rest n k rem larger))
              (values (Cons _ w tailws)
                (WinStep _ _ x rest w tk tailws tailwins)
                (AllCons _ NotPalindrome w tailws np tailabsent)))))))))

; Descend from the input length to the answer, constructing the specification's
; explicit chain of excluded lengths. This potentially expensive work erases.
(def-fns _ $ (erased fp-bounded-above : (erased (List (Nat)) xs)
    (erased (Nat) answer) (subterm erased (Nat) candidate)
    (erased (PalCenterBounds (Nil (Nat)) xs answer) bounds)
    (erased (Lt answer (Succ candidate)) le)
    (erased (NoLargerPalindrome xs candidate) above) ->
    (erased (NoLargerPalindrome xs answer) out))
  (match erased (nat-cmp answer candidate) _
    ((CEq t r a) above)
    (absurd (CGt t r a b gt) (lt-asym candidate answer gt le))
    ((CLt t r a b lt)
      (match erased candidate _
        (absurd (Zero) lt)
        ((Succ k)
          (let ((erased ws) (erased wins) (erased absent))
            (fp-bounded-windows (Nil _) xs answer k bounds lt))
          (fp-bounded-above xs answer k bounds lt
            (NoLargerStep xs k (NoPal xs candidate ws wins absent) above)))))))

(def-fns _ $ (erased fp-centers-spec : (erased (List (Nat)) xs)
    (erased (Nat) n) (erased (PalCenterBounds (Nil (Nat)) xs n) bounds)
    (erased (HasPalindromeOfLength xs n) has) ->
    (erased (LongestPalindrome xs n) correct))
  (let ((erased len) (erased lp)) (pal-length xs))
  (fp-spec-answer xs n has
    (fp-bounded-above xs n len bounds (fp-has-bound xs n len has lp)
      (NoLargerDone xs len len lp (lt-succ len)))))

; Erased histories let the runtime loops carry only numeric accumulators.
(def-adts $ (PalLcpPrefix : ((List (Nat)) fullleft fullright left right) ((Nat) n) -> Type)
  enum
  (many PLPStart : (erased (List (Nat)) left right)
    -> (PalLcpPrefix left right left right (Zero)))
  (many PLPStep : (erased (List (Nat)) fullleft fullright left right) (erased (Nat) x n)
    (erased (PalLcpPrefix fullleft fullright (Cons (Nat) x left) (Cons (Nat) x right) n) p)
    -> (PalLcpPrefix fullleft fullright left right (Succ n))))

(def-fns _ $ (erased fp-lcp-prefix-close : (erased (List (Nat)) fl fr left right)
    (erased (Nat) n k total) (subterm erased (PalLcpPrefix fl fr left right n) prefix)
    (erased (PalLcp left right k) suffix) (erased (Add n k total) sum) ->
    (erased (PalLcp fl fr total) out))
  (match erased prefix _
    ((PLPStart l r)
      (let-match erased sum (AddZero v))
      suffix)
    ((PLPStep fl0 fr0 l r x n1 p)
      (let-match erased sum (AddSucc a b c q))
      (fp-lcp-prefix-close fl fr _ _
        n1 _ total p (PLStep x _ _ _ suffix)
        (add-succ-right n1 k c q)))))

(def-adts $ (PalScanned : ((List (Nat)) xs left right) ((Nat) n) -> Type) enum
  (many PSCStart : (erased (List (Nat)) xs) (erased (Nat) n)
    -> (PalScanned xs (Nil (Nat)) xs n))
  (many PSCStep : (erased (List (Nat)) xs left right) (erased (Nat) x n e o de do)
    (erased (PalLcp left (Cons (Nat) x right) e) even)
    (erased (PalLcp left right o) odd)
    (erased (Double e de) twicee) (erased (Double o do) twiceo)
    (erased (Lt de (Succ n)) be) (erased (Lt (Succ do) (Succ n)) bo)
    (erased (PalScanned xs left (Cons (Nat) x right) n) previous)
    -> (PalScanned xs (Cons (Nat) x left) right n)))

(def-fns _ $ (erased fp-scanned-weaken : (erased (List (Nat)) xs left right)
    (erased (Nat) n m) (subterm erased (PalScanned xs left right n) scanned)
    (erased (Lt n (Succ m)) le) -> (erased (PalScanned xs left right m) out))
  (match erased scanned _
    ((PSCStart source old) (PSCStart xs m))
    ((PSCStep source l r x old e o de do even odd twicee twiceo be bo previous)
      (PSCStep xs l r x m e o de do even odd twicee twiceo
        (fp-le-trans de n m be le) (fp-le-trans _ n m bo le)
        (fp-scanned-weaken xs l _ n m previous le)))))

(def-fns _ $ (erased fp-scanned-close : (erased (List (Nat)) xs left right)
    (erased (Nat) n) (subterm erased (PalScanned xs left right n) scanned)
    (erased (PalCenterBounds left right n) remaining) ->
    (erased (PalCenterBounds (Nil (Nat)) xs n) all))
  (match erased scanned _
    ((PSCStart source bound) remaining)
    ((PSCStep source l r x bound e o de do even odd twicee twiceo be bo previous)
      (fp-scanned-close xs l _ n previous
        (PCBStep l r x n e o de do even odd twicee twiceo be bo remaining)))))
