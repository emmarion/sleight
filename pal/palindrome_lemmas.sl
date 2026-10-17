; Erased list/specification lemmas shared by the fast palindrome solver.
; Load after palindrome_relations.sl and palindrome_naive.sl.
; The simultaneous structural inductions follow self/base.sl and
; self/heap.sl's proofs of functional indexed relations.

(def-fns _ $ (erased fp-length-unique : (erased Type A)
    (erased (List A) xs) (erased (Nat) n m)
    (subterm erased (PalLength A xs n) p) (erased (PalLength A xs m) q) ->
    (erased (Eq (Nat) n m) e))
  (match erased p _
    ((PalLNil _)
      (let-match erased q (PalLNil _))
      (Refl _ (Zero)))
    ((PalLCons _ _ rest k p1)
      (let-match erased q (PalLCons _ _ _ j q1))
      (let-match erased (fp-length-unique _ rest k j p1 q1) (Refl _ _))
      (Refl _ n))))

(def-fns _ $ (erased fp-add-unique : (erased (Nat) a b c d)
    (subterm erased (Add a b c) p) (erased (Add a b d) q) ->
    (erased (Eq (Nat) c d) e))
  (match erased p _
    ((AddZero _)
      (let-match erased q (AddZero _))
      (Refl _ b))
    ((AddSucc x _ z p1)
      (let-match erased q (AddSucc _ _ z2 q1))
      (let-match erased (fp-add-unique x b z z2 p1 q1) (Refl _ _))
      (Refl _ c))))

(def-fns _ $ (erased fp-concat : (erased Type A)
    (subterm erased (List A) xs) (erased (List A) ys) ->
    (erased (List A) zs) (erased (PalConcat A xs ys zs) p))
  (let-match erased xs (Cons _ x rest) ((Nil _) (values ys (PalCatNil _ ys))))
  (let ((erased zs) (erased p)) (fp-concat _ rest ys))
  (values (Cons _ x zs) (PalCatCons _ x _ _ _ p)))

(def-fns _ $ (erased fp-concat-unique : (erased Type A)
    (erased (List A) xs ys zs ws)
    (subterm erased (PalConcat A xs ys zs) p)
    (erased (PalConcat A xs ys ws) q) -> (erased (Eq (List A) zs ws) e))
  (match erased p _
    ((PalCatNil _ _)
      (let-match erased q (PalCatNil _ _))
      (Refl _ ys))
    ((PalCatCons _ _ rest _ out p1)
      (let-match erased q (PalCatCons _ _ _ _ out2 q1))
      (let-match erased (fp-concat-unique _ rest ys out out2 p1 q1) (Refl _ _))
      (Refl _ zs))))

; Associate (xs ++ ys) ++ zs to xs ++ (ys ++ zs).
(def-fns _ $ (erased fp-concat-assoc : (erased Type A)
    (erased (List A) xs ys xy zs xyz)
    (subterm erased (PalConcat A xs ys xy) p)
    (erased (PalConcat A xy zs xyz) q) ->
    (erased (List A) yz) (erased (PalConcat A ys zs yz) r)
    (erased (PalConcat A xs yz xyz) s))
  (let-match erased p (PalCatCons _ x rest _ out p1) ((PalCatNil _ _) (values xyz q (PalCatNil _ xyz))))
  (let-match erased q (PalCatCons _ _ _ _ out2 q1))
  (let ((erased yz) (erased r) (erased s))
    (fp-concat-assoc _ rest ys out zs out2 p1 q1))
  (values yz r (PalCatCons _ x _ _ _ s)))

; Associate xs ++ (ys ++ zs) to (xs ++ ys) ++ zs.
(def-fns _ $ (erased fp-concat-unassoc : (erased Type A)
    (erased (List A) xs ys zs yz xyz)
    (subterm erased (PalConcat A xs yz xyz) p)
    (erased (PalConcat A ys zs yz) q) ->
    (erased (List A) xy) (erased (PalConcat A xs ys xy) r)
    (erased (PalConcat A xy zs xyz) s))
  (let-match erased p (PalCatCons _ x rest _ out p1) ((PalCatNil _ _) (values ys (PalCatNil _ ys) q)))
  (let ((erased xy) (erased r) (erased s))
    (fp-concat-unassoc _ rest ys zs yz out p1 q))
  (values (Cons _ x xy) (PalCatCons _ x _ _ _ r)
    (PalCatCons _ x _ _ _ s)))

(def-fns _ $ (erased fp-concat-length : (erased Type A)
    (erased (List A) xs ys zs) (erased (Nat) n m k)
    (subterm erased (PalConcat A xs ys zs) p)
    (erased (PalLength A xs n) lx) (erased (PalLength A ys m) ly)
    (erased (Add n m k) sum) -> (erased (PalLength A zs k) lz))
  (match erased p _
    ((PalCatNil _ _)
      (let-match erased lx (PalLNil _))
      (let-match erased sum (AddZero _))
      ly)
    ((PalCatCons _ x rest _ out p1)
      (let-match erased lx (PalLCons _ _ _ n1 lx1))
      (let-match erased sum (AddSucc _ _ c1 sum1))
      (PalLCons _ x _ _
        (fp-concat-length _ rest ys out n1 m c1 p1 lx1 ly sum1)))))

(def-fns _ $ (erased fp-take-concat : (erased Type A)
    (erased (List A) w rest xs) (erased (Nat) n)
    (subterm erased (PalConcat A w rest xs) cat)
    (erased (PalLength A w n) len) -> (erased (Take A n xs w) tk))
  (match erased cat _
    ((PalCatNil _ _)
      (let-match erased len (PalLNil _))
      (TakeZero _ xs))
    ((PalCatCons _ x inner _ out cat1)
      (let-match erased len (PalLCons _ _ _ k len1))
      (TakeSucc _ _ x _ _ (fp-take-concat _ inner rest out k cat1 len1)))))

(def-fns _ $ (erased fp-take-unique : (erased Type A)
    (erased (Nat) n) (erased (List A) xs w v)
    (subterm erased (Take A n xs w) p) (erased (Take A n xs v) q) ->
    (erased (Eq (List A) w v) e))
  (match erased p _
    ((TakeZero _ _)
      (let-match erased q (TakeZero _ _))
      (Refl _ w))
    ((TakeSucc _ k _ rest out p1)
      (let-match erased q (TakeSucc _ _ _ _ out2 q1))
      (let-match erased (fp-take-unique _ k rest out out2 p1 q1) (Refl _ _))
      (Refl _ w))))

(def-fns _ $ (erased fp-take-bound : (erased Type A)
    (erased (Nat) n len) (erased (List A) xs w)
    (subterm erased (Take A n xs w) tk) (erased (PalLength A xs len) p) ->
    (erased (Lt n (Succ len)) bound))
  (let-match erased tk (TakeSucc _ k _ rest out tk1) ((TakeZero _ _) (LtZ len)))
  (let-match erased p (PalLCons _ _ _ len1 p1))
  (LtS _ _ (fp-take-bound _ k len1 rest out tk1 p1)))

(def-fns _ $ (erased fp-has-bound : (erased (List (Nat)) xs)
    (erased (Nat) n len) (subterm erased (HasPalindromeOfLength xs n) h)
    (erased (PalLength (Nat) xs len) p) -> (erased (Lt n (Succ len)) bound))
  (let-match erased h (HasThere _ rest _ h1) ((HasHere _ _ w tk _) (fp-take-bound _ n len xs w tk p)))
  (let-match erased p (PalLCons _ _ _ len1 p1))
  (lt-weaken n _ (fp-has-bound rest n len1 h1 p1)))

; The fused existential really entails the existential in the original spec.
(def-fns _ $ (erased fp-has-windows : (erased (List (Nat)) xs)
    (erased (Nat) n) (erased (List (List (Nat))) ws)
    (subterm erased (Windows (Nat) n xs ws) wins)
    (erased (HasPalindromeOfLength xs n) has) ->
    (erased (Exists (List (Nat)) NatPalindrome ws) found))
  (let-match erased wins (WinStep _ _ _ rest w tk tail3 wins1)
    ((WinEmpty _)
      (ExHere _ NatPalindrome (Nil _) (Nil _)
        (IsNatPalindrome (Nil _) (PalNil _))))
    (absurd (WinStop _ _ _ len lp short)
      (lt-asym len n short (fp-has-bound xs n len has lp))))
  (let-match erased has (HasHere _ _ v tk2 pal)
    ((HasThere _ _ _ has1)
      (ExThere _ NatPalindrome w tail3
        (fp-has-windows rest n tail3 wins1 has1))))
  (let-match erased (fp-take-unique _ n xs w v tk tk2) (Refl _ _))
  (ExHere _ NatPalindrome w tail3 (IsNatPalindrome w pal)))

(def-fns _ $ (erased fp-spec-answer : (erased (List (Nat)) xs)
    (erased (Nat) n) (erased (HasPalindromeOfLength xs n) has)
    (erased (NoLargerPalindrome xs n) above) ->
    (erased (LongestPalindrome xs n) correct))
  (match erased n _
    ((Zero)
      (let ((erased ws) (erased wins) (erased found)) (pal-zero-windows xs))
      (IsLongest xs n ws wins found above))
    ((Succ k)
      (let ((erased ws) (erased wins) (erased _)) (pal-windows k xs))
      (IsLongest xs n ws wins (fp-has-windows xs n ws wins has) above))))

(def-fns _ $ (erased fp-reverse : (erased Type A)
    (subterm erased (List A) xs) ->
    (erased (List A) ys) (erased (Reverse A xs ys) rev))
  (let-match erased xs (Cons _ x rest) ((Nil _) (values (Nil _) (RevNil _))))
  (let ((erased ys) (erased p)) (fp-reverse _ rest))
  (let ((erased zs) (erased q)) (fp-concat _ ys (Cons _ x (Nil _))))
  (values zs (RevCons _ x _ _ _ p q)))

(def-fns _ $ (erased fp-reverse-unique : (erased Type A)
    (erased (List A) xs ys zs)
    (subterm erased (Reverse A xs ys) p) (erased (Reverse A xs zs) q) ->
    (erased (Eq (List A) ys zs) eq))
  (match erased p _
    ((RevNil _)
      (let-match erased q (RevNil _))
      (Refl _ ys))
    ((RevCons _ _ rest tail3 _ p1 cp)
      (let-match erased q (RevCons _ _ _ tail2 _ q1 cq))
      (let-match erased (fp-reverse-unique _ rest tail3 tail2 p1 q1) (Refl _ _))
      (fp-concat-unique _ tail3 _ ys zs cp cq))))

(def-fns _ $ (erased fp-reverse-snoc : (erased Type A)
    (erased (List A) xs ys zs) (erased A x)
    (subterm erased (Reverse A xs ys) rev)
    (erased (PalConcat A xs (Cons A x (Nil A)) zs) cat) ->
    (erased (Reverse A zs (Cons A x ys)) p))
  (match erased rev _
    ((RevNil _)
      (let-match erased cat (PalCatNil _ _))
      (RevCons _ x _ _ _
        (RevNil _) (PalCatNil _ _)))
    ((RevCons _ y rest tail3 _ r1 c1)
      (let-match erased cat (PalCatCons _ _ _ _ out2 c2))
      (RevCons _ y _ _ _
        (fp-reverse-snoc _ rest tail3 out2 x r1 c2)
        (PalCatCons _ x _ _ _ c1)))))

(def-fns _ $ (erased fp-pal-reverse : (erased Type A)
    (erased (List A) xs) (subterm erased (Palindrome A xs) pal) ->
    (erased (Reverse A xs xs) rev))
  (match erased pal _
    ((PalNil _) (RevNil _))
    ((PalOne _ x)
      (RevCons _ x _ _ _ (RevNil _) (PalCatNil _ xs)))
    ((PalWrap _ x inner withx p q)
      (RevCons _ x _ _ _
        (fp-reverse-snoc _ inner inner withx x (fp-pal-reverse _ inner p) q)
        (PalCatCons _ x _ _ _ q)))))

(def-fns _ $ (erased fp-concat-nil : (erased Type A)
    (subterm erased (List A) xs) -> (erased (PalConcat A xs (Nil A) xs) p))
  (match erased xs _
    ((Nil _) (PalCatNil _ xs))
    ((Cons _ x rest) (PalCatCons _ x _ _ _ (fp-concat-nil _ rest)))))

; Reverse distributes over concatenation, reversing the order of the pieces.
(def-fns _ $ (erased fp-reverse-concat : (erased Type A)
    (erased (List A) xs ys zs rx ry)
    (subterm erased (PalConcat A xs ys zs) cat)
    (erased (Reverse A xs rx) px) (erased (Reverse A ys ry) py) ->
    (erased (List A) rz) (erased (Reverse A zs rz) pz)
    (erased (PalConcat A ry rx rz) out))
  (match erased cat _
    ((PalCatNil _ _)
      (let-match erased px (RevNil _))
      (let ((erased rz) (erased out)) (fp-concat _ ry (Nil _)))
      (let ((erased same))
        (fp-concat-unique _ ry (Nil _) rz ry out
          (fp-concat-nil _ ry)))
      (let-match erased same (Refl _ _))
      (values ry py out))
    ((PalCatCons _ x rest _ out c1)
      (let-match erased px (RevCons _ _ _ rr _ r1 cx))
      (let ((erased rout) (erased prout) (erased crout))
        (fp-reverse-concat _ rest ys out rr ry c1 r1 py))
      (let ((erased rz) (erased cz)) (fp-concat _ rout (Cons _ x (Nil _))))
      (let ((erased rx3) (erased cx3) (erased final))
        (fp-concat-assoc _ ry rr rout _ rz crout cz))
      (let-match erased (fp-concat-unique _ rr _ rx3 rx cx3 cx) (Refl _ _))
      (values rz (RevCons _ x _ _ _ prout cz) final))))

; Manacher's positive mirror lemma, stated without index arithmetic:
; if big = before ++ window ++ after and both big and window are
; palindromes, then big = reverse(after) ++ window ++ reverse(before).
; The reflected window is literally the same list, so its Palindrome
; certificate is reusable. The negative/mismatch certificate is obtained
; by checking the first pair beyond the reused radius during expansion.
(def-fns _ $ (erased fp-pal-reflect : (erased Type A)
    (erased (List A) big before window after rest)
    (erased (Palindrome A big) bigpal)
    (erased (Palindrome A window) winpal)
    (erased (PalConcat A before rest big) prefix)
    (erased (PalConcat A window after rest) suffix) ->
    (erased (List A) rb ra rest2)
    (erased (Reverse A before rb) revbefore)
    (erased (Reverse A after ra) revafter)
    (erased (PalConcat A window rb rest2) middle)
    (erased (PalConcat A ra rest2 big) reflected))
  (let ((erased rb) (erased revbefore)) (fp-reverse _ before))
  (let ((erased ra) (erased revafter)) (fp-reverse _ after))
  (let ((erased rr) (erased revrest) (erased catrest))
    (fp-reverse-concat _ window after rest window ra suffix
      (fp-pal-reverse _ window winpal) revafter))
  (let ((erased rbig) (erased revbig) (erased catbig))
    (fp-reverse-concat _ before rest big rb rr prefix revbefore revrest))
  (let-match erased (fp-reverse-unique _ big rbig big revbig (fp-pal-reverse _ big bigpal)) (Refl _ _))
  (let ((erased tail3) (erased middle) (erased reflected))
    (fp-concat-assoc _ ra window rr rb big catrest catbig))
  (values rb ra tail3 revbefore revafter middle reflected))

; Splitting a known-length list also returns the length of the remainder.
(def-fns _ $ (erased fp-split : (erased Type A)
    (subterm erased (Nat) n) (erased (List A) xs) (erased (Nat) len)
    (erased (PalLength A xs len) size) (erased (Lt n (Succ len)) bound) ->
    (erased (List A) prefix rest) (erased (Nat) m)
    (erased (PalConcat A prefix rest xs) cat)
    (erased (PalLength A prefix n) lp) (erased (PalLength A rest m) lr)
    (erased (Add n m len) sum))
  (let-match erased n (Succ k) ((Zero) (values (Nil _) xs len (PalCatNil _ xs) (PalLNil _) size (AddZero len))))
  (match erased xs _
    (absurd (Nil _)
      (let-match erased size (PalLNil _)) (let-match erased bound (LtS _ _ q)) q)
    ((Cons _ x tail3)
      (let-match erased size (PalLCons _ _ _ len1 size1))
      (let-match erased bound (LtS _ _ bound1))
      (let ((erased prefix) (erased rest) (erased m)
           (erased cat) (erased lp) (erased lr) (erased sum))
        (fp-split _ k tail3 len1 size1 bound1))
      (values (Cons _ x prefix) rest m
        (PalCatCons _ x _ _ _ cat)
        (PalLCons _ x _ _ lp) lr (AddSucc _ _ _ sum)))))

(def-fns _ $ (erased fp-split-unique : (erased Type A)
    (erased (List A) xs p r q s) (erased (Nat) n)
    (subterm erased (PalConcat A p r xs) cp) (erased (PalConcat A q s xs) cq)
    (erased (PalLength A p n) lp) (erased (PalLength A q n) lq) ->
    (erased (Eq (List A) p q) ep) (erased (Eq (List A) r s) er))
  (match erased cp _
    ((PalCatNil _ _)
      (let-match erased lp (PalLNil _))
      (let-match erased lq (PalLNil _))
      (let-match erased cq (PalCatNil _ _))
      (values (Refl _ p) (Refl _ r)))
    ((PalCatCons _ _ pt _ out cp1)
      (let-match erased lp (PalLCons _ _ _ k lp1))
      (let-match erased lq (PalLCons _ _ qt _ lq1))
      (let-match erased cq (PalCatCons _ _ _ _ _ cq1))
      (let ((erased ep) (erased er))
        (fp-split-unique _ out pt r qt s k cp1 cq1 lp1 lq1))
      (let-match erased ep (Refl _ _))
      (values (Refl _ p) er))))

; For two prefixes of one list, the shorter prefix is a prefix of the longer.
(def-fns _ $ (erased fp-prefix-ordered : (erased Type A)
    (erased (List A) xs p r q s) (erased (Nat) n m)
    (subterm erased (PalConcat A p r xs) cp) (erased (PalConcat A q s xs) cq)
    (erased (PalLength A p n) lp) (erased (PalLength A q m) lq)
    (erased (Lt n (Succ m)) bound) ->
    (erased (List A) middle) (erased (Nat) k)
    (erased (PalConcat A p middle q) left) (erased (PalConcat A middle s r) right)
    (erased (PalLength A middle k) lm) (erased (Add n k m) sum))
  (match erased cp _
    ((PalCatNil _ _)
      (let-match erased lp (PalLNil _))
      (values q m (PalCatNil _ q) cq lq (AddZero m)))
    ((PalCatCons _ x pt _ out cp1)
      (let-match erased lp (PalLCons _ _ _ k lp1))
      (match erased lq _
        (absurd (PalLNil _)
          (let-match erased bound (LtS _ _ p2)) p2)
        ((PalLCons _ _ qt j lq1)
          (let-match erased cq (PalCatCons _ _ _ _ _ cq1))
          (let-match erased bound (LtS _ _ bound1))
          (let ((erased middle) (erased count) (erased left)
               (erased right) (erased lm) (erased sum))
            (fp-prefix-ordered _ out pt r qt s k j cp1 cq1 lp1 lq1 bound1))
          (values middle count (PalCatCons _ x _ _ _ left)
            right lm (AddSucc _ _ _ sum)))))))

(def-adts $ (PalRange : ((List (Nat)) xs) ((Nat) lo hi) ((List (Nat)) w) -> Type)
  enum
  (many MkPalRange : (erased (List (Nat)) xs p w end rest)
    (erased (Nat) lo width hi)
    (erased (PalConcat (Nat) p w end) before)
    (erased (PalConcat (Nat) end rest xs) after)
    (erased (PalLength (Nat) p lo) lp) (erased (PalLength (Nat) w width) lw)
    (erased (Add lo width hi) sum) -> (PalRange xs lo hi w)))

(def-fns _ $ (erased fp-range-total : (erased (List (Nat)) xs)
    (erased (Nat) n lo hi) (erased (PalLength (Nat) xs n) len)
    (erased (Lt lo (Succ hi)) lower) (erased (Lt hi (Succ n)) upper) ->
    (erased (List (Nat)) w) (erased (PalRange xs lo hi w) range))
  (let ((erased end) (erased rest) (erased _) (erased after)
       (erased lend) (erased _) (erased _))
    (fp-split _ hi xs n len upper))
  (let ((erased prefix) (erased w) (erased width) (erased before)
       (erased lp) (erased lw) (erased sum))
    (fp-split _ lo end hi lend lower))
  (values w (MkPalRange xs prefix w end rest lo width hi before after lp lw sum)))

(def-fns _ $ (erased fp-range-unique : (erased (List (Nat)) xs)
    (erased (Nat) lo hi) (erased (List (Nat)) w v)
    (erased (PalRange xs lo hi w) p) (erased (PalRange xs lo hi v) q) ->
    (erased (Eq (List (Nat)) w v) same))
  (let-match erased p (MkPalRange _ pre _ end rest _ width _ before after lp lw sum))
  (let-match erased q (MkPalRange _ pre2 _ end2 rest2 _ width2 _ before2 after2 lp2 lw2 sum2))
  (let ((erased eend) (erased _))
    (fp-split-unique _ xs end rest end2 rest2 hi after after2
      (fp-concat-length _ pre w end lo width hi before lp lw sum)
      (fp-concat-length _ pre2 v end2 lo width2 hi before2 lp2 lw2 sum2)))
  (let-match erased eend (Refl _ _))
  (let ((erased _) (erased ew))
    (fp-split-unique _ end pre w pre2 v lo before before2 lp lp2))
  ew)

; A contained range gives an actual prefix/window/suffix decomposition.
(def-fns _ $ (erased fp-range-inside : (erased (List (Nat)) xs big w)
    (erased (Nat) l r a b)
    (erased (PalRange xs l r big) outer) (erased (PalRange xs a b w) inner)
    (erased (Lt l (Succ a)) lower) (erased (Lt b (Succ r)) upper) ->
    (erased (List (Nat)) before after rest) (erased (Nat) nb na)
    (erased (PalConcat (Nat) before rest big) cb)
    (erased (PalConcat (Nat) w after rest) ca)
    (erased (PalLength (Nat) before nb) lb) (erased (PalLength (Nat) after na) la)
    (erased (Add l nb a) left) (erased (Add b na r) right))
  (let-match erased outer (MkPalRange _ op _ oe ot _ on _ oc1 oc2 olp olw osum))
  (let-match erased inner (MkPalRange _ ip _ ie it _ inn _ ic1 ic2 ilp ilw isum))
  (let ((erased after) (erased na) (erased cut) (erased _)
       (erased la) (erased right))
    (fp-prefix-ordered _ xs ie it oe ot b r ic2 oc2
      (fp-concat-length _ ip w ie a inn b ic1 ilp ilw isum)
      (fp-concat-length _ op big oe l on r oc1 olp olw osum) upper))
  (let ((erased rest) (erased ca) (erased newcut))
    (fp-concat-assoc _ ip w ie after oe ic1 cut))
  (let ((erased before) (erased nb) (erased _) (erased cb)
       (erased lb) (erased left))
    (fp-prefix-ordered _ oe op big ip rest l a oc1 newcut olp ilp lower))
  (values before after rest nb na cb ca lb la left right))

(def-fns _ $ (erased fp-reverse-length : (erased Type A)
    (erased (List A) xs ys) (erased (Nat) n)
    (subterm erased (Reverse A xs ys) rev) (erased (PalLength A xs n) len) ->
    (erased (PalLength A ys n) out))
  (match erased rev _
    ((RevNil _)
      (let-match erased len (PalLNil _))
      (PalLNil _))
    ((RevCons _ x rest tail3 _ r c)
      (let-match erased len (PalLCons _ _ _ k p))
      (fp-concat-length _ tail3 _ ys k (Succ (Zero)) _
        c (fp-reverse-length _ rest tail3 k r p)
        (PalLCons _ x _ _ (PalLNil _))
        (add-succ-right k (Zero) k (add-zero-right k))))))

(def-fns _ $ (erased fp-add-cancel-left : (erased (Nat) a b d c)
    (subterm erased (Add a b c) p) (erased (Add a d c) q) ->
    (erased (Eq (Nat) b d) same))
  (match erased p _
    ((AddZero _)
      (let-match erased q (AddZero _))
      (Refl _ b))
    ((AddSucc x _ z p1)
      (let-match erased q (AddSucc _ _ _ q1))
      (fp-add-cancel-left x b d z p1 q1))))

(def-fns _ $ (erased fp-range-reflect : (erased (List (Nat)) xs big w)
    (erased (Nat) l r a b newlo newhi afterN width)
    (erased (PalRange xs l r big) outer) (erased (PalRange xs a b w) inner)
    (erased (Palindrome (Nat) big) bigpal) (erased (Palindrome (Nat) w) winpal)
    (erased (Lt l (Succ a)) lower) (erased (Lt b (Succ r)) upper)
    (erased (Add b afterN r) ar) (erased (Add l afterN newlo) al)
    (erased (PalLength (Nat) w width) lw) (erased (Add newlo width newhi) ah) ->
    (erased (PalRange xs newlo newhi w) reflected))
  (let ((erased before) (erased after) (erased rest) (erased _) (erased na)
       (erased cb) (erased ca) (erased _) (erased la) (erased _) (erased right))
    (fp-range-inside xs big w l r a b outer inner lower upper))
  (let ((erased same)) (fp-add-cancel-left b na afterN r right ar))
  (let-match erased same (Refl _ _))
  (let ((erased rb) (erased ra) (erased tail3) (erased _) (erased revafter) (erased middle) (erased mirrored))
    (fp-pal-reflect _ big before w after rest bigpal winpal cb ca))
  (let-match erased outer (MkPalRange _ op _ oe ot _ _ _ oc1 oc2 olp _ _))
  (let ((erased prefix) (erased cp) (erased ct))
    (fp-concat-unassoc _ op ra tail3 big oe oc1 mirrored))
  (let ((erased end) (erased ce) (erased cr))
    (fp-concat-unassoc _ prefix w rb tail3 oe ct middle))
  (let ((erased suffix) (erased _) (erased out))
    (fp-concat-assoc _ end rb oe ot xs cr oc2))
  (MkPalRange xs prefix w end suffix newlo width newhi ce out
    (fp-concat-length _ op ra prefix l afterN newlo cp olp
      (fp-reverse-length _ after ra afterN revafter la) al)
    lw ah))
