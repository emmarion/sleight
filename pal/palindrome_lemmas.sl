; Erased list/specification lemmas shared by the fast palindrome solver.
; Load after palindrome_relations.sl and palindrome_naive.sl.
; The simultaneous structural inductions follow self/base.sl and
; self/heap.sl's proofs of functional indexed relations.

(def-fns _ $ erased fp-length-unique : (erased Type A)
    (erased (List A) xs) (erased (Nat) n m)
    (subterm erased (Length A xs n) p) (erased (Length A xs m) q) ->
    (erased (Eq (Nat) n m) e)
  (match erased p _
    ((LNil a) (match erased q _ ((LNil b) (Refl (Nat) (Zero)))))
    ((LCons a x rest k p1)
      (match erased q _
        ((LCons b y tail j q1)
          (match erased (fp-length-unique A rest k j p1 q1) _
            ((Refl t z) (Refl (Nat) n))))))))

(def-fns _ $ erased fp-add-unique : (erased (Nat) a b c d)
    (subterm erased (Add a b c) p) (erased (Add a b d) q) ->
    (erased (Eq (Nat) c d) e)
  (match erased p _
    ((AddZero x) (match erased q _ ((AddZero y) (Refl (Nat) b))))
    ((AddSucc x y z p1)
      (match erased q _
        ((AddSucc x2 y2 z2 q1)
          (match erased (fp-add-unique x b z z2 p1 q1) _
            ((Refl t v) (Refl (Nat) c))))))))

(def-fns _ $ erased fp-concat : (erased Type A)
    (subterm erased (List A) xs) (erased (List A) ys) ->
    (erased (List A) zs) (erased (Concat A xs ys zs) p)
  (match erased xs _
    ((Nil a) (values ys (CatNil A ys)))
    ((Cons a x rest)
      (let (erased zs) (erased p) (fp-concat A rest ys))
      (values (Cons A x zs) (CatCons A x rest ys zs p)))))

(def-fns _ $ erased fp-concat-unique : (erased Type A)
    (erased (List A) xs ys zs ws)
    (subterm erased (Concat A xs ys zs) p)
    (erased (Concat A xs ys ws) q) -> (erased (Eq (List A) zs ws) e)
  (match erased p _
    ((CatNil a tail) (match erased q _ ((CatNil b tail2) (Refl (List A) ys))))
    ((CatCons a x rest tail out p1)
      (match erased q _
        ((CatCons b y rest2 tail2 out2 q1)
          (match erased (fp-concat-unique A rest ys out out2 p1 q1) _
            ((Refl t v) (Refl (List A) zs))))))))

; Associate (xs ++ ys) ++ zs to xs ++ (ys ++ zs).
(def-fns _ $ erased fp-concat-assoc : (erased Type A)
    (erased (List A) xs ys xy zs xyz)
    (subterm erased (Concat A xs ys xy) p)
    (erased (Concat A xy zs xyz) q) ->
    (erased (List A) yz) (erased (Concat A ys zs yz) r)
    (erased (Concat A xs yz xyz) s)
  (match erased p _
    ((CatNil a tail) (values xyz q (CatNil A xyz)))
    ((CatCons a x rest tail out p1)
      (match erased q _
        ((CatCons b y rest2 tail2 out2 q1)
          (let (erased yz) (erased r) (erased s)
            (fp-concat-assoc A rest ys out zs out2 p1 q1))
          (values yz r (CatCons A x rest yz out2 s)))))))

; Associate xs ++ (ys ++ zs) to (xs ++ ys) ++ zs.
(def-fns _ $ erased fp-concat-unassoc : (erased Type A)
    (erased (List A) xs ys zs yz xyz)
    (subterm erased (Concat A xs yz xyz) p)
    (erased (Concat A ys zs yz) q) ->
    (erased (List A) xy) (erased (Concat A xs ys xy) r)
    (erased (Concat A xy zs xyz) s)
  (match erased p _
    ((CatNil a tail) (values ys (CatNil A ys) q))
    ((CatCons a x rest tail out p1)
      (let (erased xy) (erased r) (erased s)
        (fp-concat-unassoc A rest ys zs yz out p1 q))
      (values (Cons A x xy) (CatCons A x rest ys xy r)
        (CatCons A x xy zs out s)))))

(def-fns _ $ erased fp-concat-length : (erased Type A)
    (erased (List A) xs ys zs) (erased (Nat) n m k)
    (subterm erased (Concat A xs ys zs) p)
    (erased (Length A xs n) lx) (erased (Length A ys m) ly)
    (erased (Add n m k) sum) -> (erased (Length A zs k) lz)
  (match erased p _
    ((CatNil a tail)
      (match erased lx _
        ((LNil b) (match erased sum _ ((AddZero c) ly)))))
    ((CatCons a x rest tail out p1)
      (match erased lx _
        ((LCons b y tail2 n1 lx1)
          (match erased sum _
            ((AddSucc a1 b1 c1 sum1)
              (LCons A x out c1
                (fp-concat-length A rest ys out n1 m c1 p1 lx1 ly sum1)))))))))

(def-fns _ $ erased fp-take-concat : (erased Type A)
    (erased (List A) w rest xs) (erased (Nat) n)
    (subterm erased (Concat A w rest xs) cat)
    (erased (Length A w n) len) -> (erased (Take A n xs w) tk)
  (match erased cat _
    ((CatNil a tail) (match erased len _ ((LNil b) (TakeZero A xs))))
    ((CatCons a x inner tail out cat1)
      (match erased len _
        ((LCons b y inner2 k len1)
          (TakeSucc A k x out inner (fp-take-concat A inner rest out k cat1 len1)))))))

(def-fns _ $ erased fp-take-unique : (erased Type A)
    (erased (Nat) n) (erased (List A) xs w v)
    (subterm erased (Take A n xs w) p) (erased (Take A n xs v) q) ->
    (erased (Eq (List A) w v) e)
  (match erased p _
    ((TakeZero a source) (match erased q _ ((TakeZero b source2) (Refl (List A) w))))
    ((TakeSucc a k x rest out p1)
      (match erased q _
        ((TakeSucc b j y tail out2 q1)
          (match erased (fp-take-unique A k rest out out2 p1 q1) _
            ((Refl t v) (Refl (List A) w))))))))

(def-fns _ $ erased fp-take-bound : (erased Type A)
    (erased (Nat) n len) (erased (List A) xs w)
    (subterm erased (Take A n xs w) tk) (erased (Length A xs len) p) ->
    (erased (Lt n (Succ len)) bound)
  (match erased tk _
    ((TakeZero a source) (LtZ len))
    ((TakeSucc a k x rest out tk1)
      (match erased p _
        ((LCons b y tail len1 p1)
          (LtS k (Succ len1) (fp-take-bound A k len1 rest out tk1 p1)))))))

(def-fns _ $ erased fp-has-bound : (erased (List (Nat)) xs)
    (erased (Nat) n len) (subterm erased (HasPalindromeOfLength xs n) h)
    (erased (Length (Nat) xs len) p) -> (erased (Lt n (Succ len)) bound)
  (match erased h _
    ((HasHere source k w tk pal) (fp-take-bound (Nat) n len xs w tk p))
    ((HasThere x rest k h1)
      (match erased p _
        ((LCons a y tail len1 p1)
          (lt-weaken n (Succ len1) (fp-has-bound rest n len1 h1 p1)))))))

; The fused existential really entails the existential in the original spec.
(def-fns _ $ erased fp-has-windows : (erased (List (Nat)) xs)
    (erased (Nat) n) (erased (List (List (Nat))) ws)
    (subterm erased (Windows (Nat) n xs ws) wins)
    (erased (HasPalindromeOfLength xs n) has) ->
    (erased (Exists (List (Nat)) NatPalindrome ws) found)
  (match erased wins _
    ((WinEmpty a)
      (ExHere (List (Nat)) NatPalindrome (Nil (Nat)) (Nil (List (Nat)))
        (IsNatPalindrome (Nil (Nat)) (PalNil (Nat)))))
    (absurd (WinStop a k source len lp short)
      (lt-asym len n short (fp-has-bound xs n len has lp)))
    ((WinStep a k x rest w tk tail wins1)
      (match erased has _
        ((HasHere source k2 v tk2 pal)
          (match erased (fp-take-unique (Nat) n xs w v tk tk2) _
            ((Refl t z)
              (ExHere (List (Nat)) NatPalindrome w tail (IsNatPalindrome w pal)))))
        ((HasThere y rest2 k2 has1)
          (ExThere (List (Nat)) NatPalindrome w tail
            (fp-has-windows rest n tail wins1 has1)))))))

(def-fns _ $ erased fp-spec-answer : (erased (List (Nat)) xs)
    (erased (Nat) n) (erased (HasPalindromeOfLength xs n) has)
    (erased (NoLargerPalindrome xs n) above) ->
    (erased (LongestPalindrome xs n) correct)
  (match erased n _
    ((Zero)
      (let (erased ws) (erased wins) (erased found) (pal-zero-windows xs))
      (IsLongest xs n ws wins found above))
    ((Succ k)
      (let (erased ws) (erased wins) (erased decision) (pal-windows k xs))
      (IsLongest xs n ws wins (fp-has-windows xs n ws wins has) above))))

(def-fns _ $ erased fp-reverse : (erased Type A)
    (subterm erased (List A) xs) ->
    (erased (List A) ys) (erased (Reverse A xs ys) rev)
  (match erased xs _
    ((Nil a) (values (Nil A) (RevNil A)))
    ((Cons a x rest)
      (let (erased ys) (erased p) (fp-reverse A rest))
      (let (erased zs) (erased q) (fp-concat A ys (Cons A x (Nil A))))
      (values zs (RevCons A x rest ys zs p q)))))

(def-fns _ $ erased fp-reverse-unique : (erased Type A)
    (erased (List A) xs ys zs)
    (subterm erased (Reverse A xs ys) p) (erased (Reverse A xs zs) q) ->
    (erased (Eq (List A) ys zs) eq)
  (match erased p _
    ((RevNil a) (match erased q _ ((RevNil b) (Refl (List A) ys))))
    ((RevCons a x rest tail out p1 cp)
      (match erased q _
        ((RevCons b y rest2 tail2 out2 q1 cq)
          (match erased (fp-reverse-unique A rest tail tail2 p1 q1) _
            ((Refl t v) (fp-concat-unique A tail (Cons A x (Nil A)) ys zs cp cq))))))))

(def-fns _ $ erased fp-reverse-snoc : (erased Type A)
    (erased (List A) xs ys zs) (erased A x)
    (subterm erased (Reverse A xs ys) rev)
    (erased (Concat A xs (Cons A x (Nil A)) zs) cat) ->
    (erased (Reverse A zs (Cons A x ys)) p)
  (match erased rev _
    ((RevNil a)
      (match erased cat _
        ((CatNil b tail)
          (RevCons A x (Nil A) (Nil A) (Cons A x (Nil A))
            (RevNil A) (CatNil A (Cons A x (Nil A)))))))
    ((RevCons a y rest tail out r1 c1)
      (match erased cat _
        ((CatCons b z rest2 tail2 out2 c2)
          (RevCons A y out2 (Cons A x tail) (Cons A x ys)
            (fp-reverse-snoc A rest tail out2 x r1 c2)
            (CatCons A x tail (Cons A y (Nil A)) ys c1)))))))

(def-fns _ $ erased fp-pal-reverse : (erased Type A)
    (erased (List A) xs) (subterm erased (Palindrome A xs) pal) ->
    (erased (Reverse A xs xs) rev)
  (match erased pal _
    ((PalNil a) (RevNil A))
    ((PalOne a x)
      (RevCons A x (Nil A) (Nil A) xs (RevNil A) (CatNil A xs)))
    ((PalWrap a x inner withx p q)
      (RevCons A x withx (Cons A x inner) xs
        (fp-reverse-snoc A inner inner withx x (fp-pal-reverse A inner p) q)
        (CatCons A x inner (Cons A x (Nil A)) withx q)))))

(def-fns _ $ erased fp-concat-nil : (erased Type A)
    (subterm erased (List A) xs) -> (erased (Concat A xs (Nil A) xs) p)
  (match erased xs _
    ((Nil a) (CatNil A xs))
    ((Cons a x rest) (CatCons A x rest (Nil A) rest (fp-concat-nil A rest)))))

; Reverse distributes over concatenation, reversing the order of the pieces.
(def-fns _ $ erased fp-reverse-concat : (erased Type A)
    (erased (List A) xs ys zs rx ry)
    (subterm erased (Concat A xs ys zs) cat)
    (erased (Reverse A xs rx) px) (erased (Reverse A ys ry) py) ->
    (erased (List A) rz) (erased (Reverse A zs rz) pz)
    (erased (Concat A ry rx rz) out)
  (match erased cat _
    ((CatNil a tail)
      (match erased px _
        ((RevNil b)
          (let (erased rz) (erased out) (fp-concat A ry (Nil A)))
          (let (erased same)
            (fp-concat-unique A ry (Nil A) rz ry out
              (fp-concat-nil A ry)))
          (match erased same _ ((Refl t v) (values ry py out))))))
    ((CatCons a x rest tail out c1)
      (match erased px _
        ((RevCons b y rest2 rr rx2 r1 cx)
          (let (erased rout) (erased prout) (erased crout)
            (fp-reverse-concat A rest ys out rr ry c1 r1 py))
          (let (erased rz) (erased cz) (fp-concat A rout (Cons A x (Nil A))))
          (let (erased rx3) (erased cx3) (erased final)
            (fp-concat-assoc A ry rr rout (Cons A x (Nil A)) rz crout cz))
          (match erased (fp-concat-unique A rr (Cons A x (Nil A)) rx3 rx cx3 cx) _
            ((Refl t v)
              (values rz (RevCons A x out rout rz prout cz) final))))))))

; Manacher's positive mirror lemma, stated without index arithmetic:
; if big = before ++ window ++ after and both big and window are
; palindromes, then big = reverse(after) ++ window ++ reverse(before).
; The reflected window is literally the same list, so its Palindrome
; certificate is reusable. The negative/mismatch certificate is obtained
; by checking the first pair beyond the reused radius during expansion.
(def-fns _ $ erased fp-pal-reflect : (erased Type A)
    (erased (List A) big before window after rest)
    (erased (Palindrome A big) bigpal)
    (erased (Palindrome A window) winpal)
    (erased (Concat A before rest big) prefix)
    (erased (Concat A window after rest) suffix) ->
    (erased (List A) rb ra tail)
    (erased (Reverse A before rb) revbefore)
    (erased (Reverse A after ra) revafter)
    (erased (Concat A window rb tail) middle)
    (erased (Concat A ra tail big) reflected)
  (let (erased rb) (erased revbefore) (fp-reverse A before))
  (let (erased ra) (erased revafter) (fp-reverse A after))
  (let (erased rr) (erased revrest) (erased catrest)
    (fp-reverse-concat A window after rest window ra suffix
      (fp-pal-reverse A window winpal) revafter))
  (let (erased rbig) (erased revbig) (erased catbig)
    (fp-reverse-concat A before rest big rb rr prefix revbefore revrest))
  (match erased (fp-reverse-unique A big rbig big revbig (fp-pal-reverse A big bigpal)) _
    ((Refl t v)
      (let (erased tail) (erased middle) (erased reflected)
        (fp-concat-assoc A ra window rr rb big catrest catbig))
      (values rb ra tail revbefore revafter middle reflected))))

; Splitting a known-length list also returns the length of the remainder.
(def-fns _ $ erased fp-split : (erased Type A)
    (subterm erased (Nat) n) (erased (List A) xs) (erased (Nat) len)
    (erased (Length A xs len) size) (erased (Lt n (Succ len)) bound) ->
    (erased (List A) prefix rest) (erased (Nat) m)
    (erased (Concat A prefix rest xs) cat)
    (erased (Length A prefix n) lp) (erased (Length A rest m) lr)
    (erased (Add n m len) sum)
  (match erased n _
    ((Zero) (values (Nil A) xs len (CatNil A xs) (LNil A) size (AddZero len)))
    ((Succ k)
      (match erased xs _
        (absurd (Nil a)
          (match erased size (((False) f))
            ((LNil b) (match erased bound _ ((LtS x y q) (match erased q _))))))
        ((Cons a x tail)
          (match erased size _
            ((LCons b y tail2 len1 size1)
              (match erased bound _
                ((LtS u v bound1)
                  (let (erased prefix) (erased rest) (erased m)
                       (erased cat) (erased lp) (erased lr) (erased sum)
                    (fp-split A k tail len1 size1 bound1))
                  (values (Cons A x prefix) rest m
                    (CatCons A x prefix rest tail cat)
                    (LCons A x prefix k lp) lr (AddSucc k m len1 sum)))))))))))

(def-fns _ $ erased fp-split-unique : (erased Type A)
    (erased (List A) xs p r q s) (erased (Nat) n)
    (subterm erased (Concat A p r xs) cp) (erased (Concat A q s xs) cq)
    (erased (Length A p n) lp) (erased (Length A q n) lq) ->
    (erased (Eq (List A) p q) ep) (erased (Eq (List A) r s) er)
  (match erased cp _
    ((CatNil a tail)
      (match erased lp _
        ((LNil b)
          (match erased lq _
            ((LNil c) (match erased cq _
              ((CatNil d tail2) (values (Refl (List A) p) (Refl (List A) r)))))))))
    ((CatCons a x pt tail out cp1)
      (match erased lp _
        ((LCons b y pt2 k lp1)
          (match erased lq _
            ((LCons c z qt j lq1)
              (match erased cq _
                ((CatCons d v qt2 tail2 out2 cq1)
                  (let (erased ep) (erased er)
                    (fp-split-unique A out pt r qt s k cp1 cq1 lp1 lq1))
                  (match erased ep _
                    ((Refl t w) (values (Refl (List A) p) er))))))))))))

; For two prefixes of one list, the shorter prefix is a prefix of the longer.
(def-fns _ $ erased fp-prefix-ordered : (erased Type A)
    (erased (List A) xs p r q s) (erased (Nat) n m)
    (subterm erased (Concat A p r xs) cp) (erased (Concat A q s xs) cq)
    (erased (Length A p n) lp) (erased (Length A q m) lq)
    (erased (Lt n (Succ m)) bound) ->
    (erased (List A) middle) (erased (Nat) k)
    (erased (Concat A p middle q) left) (erased (Concat A middle s r) right)
    (erased (Length A middle k) lm) (erased (Add n k m) sum)
  (match erased cp _
    ((CatNil a tail)
      (match erased lp _
        ((LNil b) (values q m (CatNil A q) cq lq (AddZero m)))))
    ((CatCons a x pt tail out cp1)
      (match erased lp _
        ((LCons b y pt2 k lp1)
          (match erased lq _
            (absurd (LNil c)
              (match erased bound (((False) f)) ((LtS u v p) (match erased p _))))
            ((LCons c z qt j lq1)
              (match erased cq _
                ((CatCons d v qt2 tail2 out2 cq1)
                  (match erased bound _
                    ((LtS u v bound1)
                      (let (erased middle) (erased count) (erased left)
                           (erased right) (erased lm) (erased sum)
                        (fp-prefix-ordered A out pt r qt s k j cp1 cq1 lp1 lq1 bound1))
                      (values middle count (CatCons A x pt middle qt left)
                        right lm (AddSucc k count j sum)))))))))))))

(def-adts $ PalRange : ((List (Nat)) xs) ((Nat) lo hi) ((List (Nat)) w) -> Type
  enum
  (many MkPalRange : (erased (List (Nat)) xs p w end rest)
    (erased (Nat) lo width hi)
    (erased (Concat (Nat) p w end) before)
    (erased (Concat (Nat) end rest xs) after)
    (erased (Length (Nat) p lo) lp) (erased (Length (Nat) w width) lw)
    (erased (Add lo width hi) sum) -> (PalRange xs lo hi w)))

(def-fns _ $ erased fp-range-total : (erased (List (Nat)) xs)
    (erased (Nat) n lo hi) (erased (Length (Nat) xs n) len)
    (erased (Lt lo (Succ hi)) lower) (erased (Lt hi (Succ n)) upper) ->
    (erased (List (Nat)) w) (erased (PalRange xs lo hi w) range)
  (let (erased end) (erased rest) (erased tailn) (erased after)
       (erased lend) (erased lrest) (erased sum1)
    (fp-split (Nat) hi xs n len upper))
  (let (erased prefix) (erased w) (erased width) (erased before)
       (erased lp) (erased lw) (erased sum)
    (fp-split (Nat) lo end hi lend lower))
  (values w (MkPalRange xs prefix w end rest lo width hi before after lp lw sum)))

(def-fns _ $ erased fp-range-unique : (erased (List (Nat)) xs)
    (erased (Nat) lo hi) (erased (List (Nat)) w v)
    (erased (PalRange xs lo hi w) p) (erased (PalRange xs lo hi v) q) ->
    (erased (Eq (List (Nat)) w v) same)
  (match erased p _
    ((MkPalRange src pre win end rest l width h before after lp lw sum)
      (match erased q _
        ((MkPalRange src2 pre2 win2 end2 rest2 l2 width2 h2 before2 after2 lp2 lw2 sum2)
          (let (erased eend) (erased erest)
            (fp-split-unique (Nat) xs end rest end2 rest2 hi after after2
              (fp-concat-length (Nat) pre w end lo width hi before lp lw sum)
              (fp-concat-length (Nat) pre2 v end2 lo width2 hi before2 lp2 lw2 sum2)))
          (match erased eend _
            ((Refl t a)
              (let (erased ep) (erased ew)
                (fp-split-unique (Nat) end pre w pre2 v lo before before2 lp lp2))
              ew)))))))

; A contained range gives an actual prefix/window/suffix decomposition.
(def-fns _ $ erased fp-range-inside : (erased (List (Nat)) xs big w)
    (erased (Nat) l r a b)
    (erased (PalRange xs l r big) outer) (erased (PalRange xs a b w) inner)
    (erased (Lt l (Succ a)) lower) (erased (Lt b (Succ r)) upper) ->
    (erased (List (Nat)) before after rest) (erased (Nat) nb na)
    (erased (Concat (Nat) before rest big) cb)
    (erased (Concat (Nat) w after rest) ca)
    (erased (Length (Nat) before nb) lb) (erased (Length (Nat) after na) la)
    (erased (Add l nb a) left) (erased (Add b na r) right)
  (match erased outer _
    ((MkPalRange src op ow oe ot ol on oh oc1 oc2 olp olw osum)
      (match erased inner _
        ((MkPalRange src2 ip iw ie it il inn ih ic1 ic2 ilp ilw isum)
          (let (erased after) (erased na) (erased cut) (erased remain)
               (erased la) (erased right)
            (fp-prefix-ordered (Nat) xs ie it oe ot b r ic2 oc2
              (fp-concat-length (Nat) ip w ie a inn b ic1 ilp ilw isum)
              (fp-concat-length (Nat) op big oe l on r oc1 olp olw osum) upper))
          (let (erased rest) (erased ca) (erased newcut)
            (fp-concat-assoc (Nat) ip w ie after oe ic1 cut))
          (let (erased before) (erased nb) (erased beforecut) (erased cb)
               (erased lb) (erased left)
            (fp-prefix-ordered (Nat) oe op big ip rest l a oc1 newcut olp ilp lower))
          (values before after rest nb na cb ca lb la left right))))))

(def-fns _ $ erased fp-reverse-length : (erased Type A)
    (erased (List A) xs ys) (erased (Nat) n)
    (subterm erased (Reverse A xs ys) rev) (erased (Length A xs n) len) ->
    (erased (Length A ys n) out)
  (match erased rev _
    ((RevNil a) (match erased len _ ((LNil b) (LNil A))))
    ((RevCons a x rest tail out r c)
      (match erased len _
        ((LCons b y rest2 k p)
          (fp-concat-length A tail (Cons A x (Nil A)) ys k (Succ (Zero)) (Succ k)
            c (fp-reverse-length A rest tail k r p)
            (LCons A x (Nil A) (Zero) (LNil A))
            (add-succ-right k (Zero) k (add-zero-right k))))))))

(def-fns _ $ erased fp-add-cancel-left : (erased (Nat) a b d c)
    (subterm erased (Add a b c) p) (erased (Add a d c) q) ->
    (erased (Eq (Nat) b d) same)
  (match erased p _
    ((AddZero x) (match erased q _ ((AddZero y) (Refl (Nat) b))))
    ((AddSucc x y z p1)
      (match erased q _
        ((AddSucc x2 y2 z2 q1) (fp-add-cancel-left x b d z p1 q1))))))

(def-fns _ $ erased fp-range-reflect : (erased (List (Nat)) xs big w)
    (erased (Nat) l r a b newlo newhi afterN width)
    (erased (PalRange xs l r big) outer) (erased (PalRange xs a b w) inner)
    (erased (Palindrome (Nat) big) bigpal) (erased (Palindrome (Nat) w) winpal)
    (erased (Lt l (Succ a)) lower) (erased (Lt b (Succ r)) upper)
    (erased (Add b afterN r) ar) (erased (Add l afterN newlo) al)
    (erased (Length (Nat) w width) lw) (erased (Add newlo width newhi) ah) ->
    (erased (PalRange xs newlo newhi w) reflected)
  (let (erased before) (erased after) (erased rest) (erased nb) (erased na)
       (erased cb) (erased ca) (erased lb) (erased la) (erased left) (erased right)
    (fp-range-inside xs big w l r a b outer inner lower upper))
  (let (erased same) (fp-add-cancel-left b na afterN r right ar))
      (match erased same _
        ((Refl t v)
          (let (erased rb) (erased ra) (erased tail) (erased revbefore) (erased revafter) (erased middle) (erased mirrored)
            (fp-pal-reflect (Nat) big before w after rest bigpal winpal cb ca))
          (match erased outer _
            ((MkPalRange src op ow oe ot ol on oh oc1 oc2 olp olw osum)
              (let (erased prefix) (erased cp) (erased ct)
                (fp-concat-unassoc (Nat) op ra tail big oe oc1 mirrored))
              (let (erased end) (erased ce) (erased cr)
                (fp-concat-unassoc (Nat) prefix w rb tail oe ct middle))
              (let (erased suffix) (erased cs) (erased out)
                (fp-concat-assoc (Nat) end rb oe ot xs cr oc2))
              (MkPalRange xs prefix w end suffix newlo width newhi ce out
                (fp-concat-length (Nat) op ra prefix l afterN newlo cp olp
                  (fp-reverse-length (Nat) after ra afterN revafter la) al)
                lw ah))))))
