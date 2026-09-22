; The positive certificates used when Manacher starts expansion at a reused
; mirror radius. Depends on palindrome_lemmas.sl and palindrome_centers.sl.

(def-adts $ (PalParity : ((Nat) extra) -> Type) enum
  (many PPEven : -> (PalParity (Zero)))
  (many PPOdd : -> (PalParity (Succ (Zero)))))

(def-fns _ $ (erased fp-split-decomp : (erased (List (Nat)) xs left right)
    (subterm erased (PalSplit xs left right) split) ->
    (erased (List (Nat)) prefix)
    (erased (PalConcat (Nat) prefix right xs) cat)
    (erased (Reverse (Nat) prefix left) rev))
  (match erased split _
    ((PSStart source) (values (Nil _) (PalCatNil _ xs) (RevNil _)))
    ((PSStep source l r x p)
      (let ((erased prefix) (erased cat) (erased rev))
        (fp-split-decomp xs l _ p))
      (let ((erased out) (erased snoc) (erased final))
        (fp-concat-unassoc _ prefix _ right
          _ xs cat
          (PalCatCons _ x _ _ _ (PalCatNil _ right))))
      (values out final (fp-reverse-snoc _ prefix l out x rev snoc)))))

(def-fns _ $ (erased fp-reverse-involutive : (erased Type A)
    (erased (List A) xs ys) (subterm erased (Reverse A xs ys) rev) ->
    (erased (Reverse A ys xs) back))
  (match erased rev _
    ((RevNil a) (RevNil _))
    ((RevCons a x rest tail3 out p q)
      (fp-reverse-snoc _ tail3 rest ys x (fp-reverse-involutive _ rest tail3 p) q))))

; Split a palindrome into equal-length reversed halves and a 0/1-element middle.
(def-fns _ $ (erased fp-pal-halves : (erased (List (Nat)) w)
    (erased (Nat) k d extra width)
    (subterm erased (Palindrome (Nat) w) pal)
    (erased (PalLength (Nat) w width) len)
    (erased (Double k d) twice) (erased (Add d extra width) sum)
    (erased (PalParity extra) parity) ->
    (erased (List (Nat)) lh mid rh mr)
    (erased (PalConcat (Nat) lh mr w) catleft)
    (erased (PalConcat (Nat) mid rh mr) catright)
    (erased (PalLength (Nat) lh k) ll) (erased (PalLength (Nat) rh k) lr)
    (erased (PalLength (Nat) mid extra) lm)
    (erased (Reverse (Nat) lh rh) rev))
  (match erased pal _
    ((PalNil a)
      (let-match erased len (PalLNil b))
      (let-match erased sum (AddZero v))
      (let-match erased twice (D0))
      (values (Nil _) (Nil _) (Nil _) (Nil _)
        (PalCatNil _ (Nil _)) (PalCatNil _ (Nil _))
        (PalLNil _) (PalLNil _) (PalLNil _) (RevNil _)))
    ((PalOne a x)
      (let-match erased len (PalLCons b y rest j lp))
      (let-match erased lp (PalLNil c))
      (match erased twice _
        ((D0)
          (let-match erased sum (AddZero v))
          (values (Nil _) w (Nil _) w
            (PalCatNil _ w) (fp-concat-nil _ w)
            (PalLNil _) (PalLNil _) len (RevNil _)))
        (absurd (DS a2 b2 p)
          (match erased sum (((False) f))
            ((AddSucc a3 b3 c3 p3) (match erased p3 _))))))
    ((PalWrap a x inner withx innerpal snoc)
      (let ((erased ni) (erased li)) (pal-length inner))
      (let ((erased withlen))
        (fp-concat-length _ inner _ withx
          ni (Succ (Zero)) _ snoc li
          (PalLCons _ x _ _ (PalLNil _))
          (add-succ-right ni (Zero) ni (add-zero-right ni))))
      (let-match erased (fp-length-unique _ w width _ len
                      (PalLCons _ x _ _ withlen)) (Refl t v))
      (match erased twice _
        (absurd (D0)
          (match erased sum (((False) f)) ((AddZero _) (match erased parity _))))
        ((DS k1 d1 twice1)
          (let-match erased sum (AddSucc a1 b1 c1 sum1))
          (let-match erased sum1 (AddSucc a2 b2 c2 sum2))
          (let ((erased lh) (erased mid) (erased rh) (erased mr)
               (erased cl) (erased cr) (erased ll) (erased lr) (erased lm) (erased rev))
            (fp-pal-halves inner k1 d1 extra ni innerpal li twice1 sum2 parity))
          (let ((erased mr2) (erased mrSnoc) (erased cl2))
            (fp-concat-assoc _ lh mr inner _ withx cl snoc))
          (let ((erased rh2) (erased rhSnoc) (erased cr2))
            (fp-concat-assoc _ mid rh mr _ mr2 cr mrSnoc))
          (values (Cons _ x lh) mid rh2 mr2
            (PalCatCons _ x _ _ _ cl2) cr2
            (PalLCons _ x _ _ ll)
            (fp-concat-length _ rh _ rh2
              k1 (Succ (Zero)) _ rhSnoc lr
              (PalLCons _ x _ _ (PalLNil _))
              (add-succ-right k1 (Zero) k1 (add-zero-right k1)))
            lm (RevCons _ x _ _ _ rev rhSnoc)))))))

; Remove the same number of elements from both ends of a palindrome.
; sum states that the two removed margins and the desired middle exhaust it.
(def-fns _ $ (erased fp-pal-trim : (erased (List (Nat)) w)
    (subterm erased (Nat) cut) (erased (Nat) dc target width)
    (erased (Palindrome (Nat) w) pal) (erased (PalLength (Nat) w width) len)
    (erased (Double cut dc) twice) (erased (Add dc target width) sum) ->
    (erased (List (Nat)) before middle after rest)
    (erased (PalConcat (Nat) before rest w) cb)
    (erased (PalConcat (Nat) middle after rest) ca)
    (erased (PalLength (Nat) before cut) lb) (erased (PalLength (Nat) after cut) la)
    (erased (PalLength (Nat) middle target) lm) (erased (Palindrome (Nat) middle) pm))
  (match erased cut _
    ((Zero)
      (let-match erased twice (D0))
      (let-match erased sum (AddZero v))
      (values (Nil _) w (Nil _) w
        (PalCatNil _ w) (fp-concat-nil _ w)
        (PalLNil _) (PalLNil _) len pal))
    ((Succ c)
      (let-match erased twice (DS c1 d1 twice1))
      (let-match erased sum (AddSucc a b s sum1))
      (let-match erased sum1 (AddSucc a2 b2 s2 sum2))
      (match erased pal _
        (absurd (PalNil t) (match erased len (((False) f))))
        (absurd (PalOne t x)
          (match erased len (((False) f))
            ((PalLCons t2 x2 rest k p) (match erased p _))))
        ((PalWrap t x inner withx pi snoc)
          (let ((erased ni) (erased li)) (pal-length inner))
          (let ((erased lwith))
            (fp-concat-length _ inner _ withx
              ni (Succ (Zero)) _ snoc li
              (PalLCons _ x _ _ (PalLNil _))
              (add-succ-right ni (Zero) ni (add-zero-right ni))))
          (let-match erased (fp-length-unique _ w width _ len
                          (PalLCons _ x _ _ lwith)) (Refl t3 v))
          (let ((erased before) (erased middle) (erased after) (erased rest)
               (erased cb) (erased ca) (erased lb) (erased la) (erased lm) (erased pm))
            (fp-pal-trim inner c d1 target ni pi li twice1 sum2))
          (let ((erased rest2) (erased restSnoc) (erased cb2))
            (fp-concat-assoc _ before rest inner _ withx cb snoc))
          (let ((erased after2) (erased afterSnoc) (erased ca2))
            (fp-concat-assoc _ middle after rest _ rest2 ca restSnoc))
          (values (Cons _ x before) middle after2 rest2
            (PalCatCons _ x _ _ _ cb2) ca2
            (PalLCons _ x _ _ lb)
            (fp-concat-length _ after _ after2
              c (Succ (Zero)) _ afterSnoc la
              (PalLCons _ x _ _ (PalLNil _))
              (add-succ-right c (Zero) c (add-zero-right c))) lm pm))))))

(def-fns _ $ (erased fp-concat-add : (erased Type A)
    (erased (List A) xs ys zs) (erased (Nat) n m k)
    (subterm erased (PalConcat A xs ys zs) cat)
    (erased (PalLength A xs n) lx) (erased (PalLength A ys m) ly)
    (erased (PalLength A zs k) lz) -> (erased (Add n m k) sum))
  (match erased cat _
    ((PalCatNil a _)
      (let-match erased lx (PalLNil b))
      (let-match erased (fp-length-unique _ ys m k ly lz) (Refl t v))
      (AddZero m))
    ((PalCatCons a x rest _ out cat1)
      (let-match erased lx (PalLCons b y rest2 n1 lx1))
      (let-match erased lz (PalLCons c z out2 k1 lz1))
      (AddSucc _ _ _ (fp-concat-add _ rest ys out n1 m k1 cat1 lx1 ly lz1)))))

(def-fns _ $ (erased fp-add-cancel-right : (erased (Nat) a b c total)
    (erased (Add a c total) p) (erased (Add b c total) q) ->
    (erased (Eq (Nat) a b) same))
  (fp-add-cancel-left c a b total (add-comm a c total p) (add-comm b c total q)))

; Put a trimmed decomposition back into the original input's coordinates.
(def-fns _ $ (erased fp-trim-range : (erased (List (Nat)) xs w before middle after rest)
    (erased (Nat) lo hi cut newlo newhi width)
    (erased (PalRange xs lo hi w) range)
    (erased (PalConcat (Nat) before rest w) cb)
    (erased (PalConcat (Nat) middle after rest) ca)
    (erased (PalLength (Nat) before cut) lb) (erased (PalLength (Nat) after cut) la)
    (erased (PalLength (Nat) middle width) lm)
    (erased (Add lo cut newlo) al) (erased (Add newhi cut hi) ah)
    (erased (Add newlo width newhi) size) ->
    (erased (PalRange xs newlo newhi middle) out))
  (let-match erased range (MkPalRange source op ow oe ot ol on oh oc1 oc2 olp olw osum))
  (let ((erased prefix) (erased cp) (erased cr))
    (fp-concat-unassoc _ op before rest w oe oc1 cb))
  (let ((erased end) (erased ce) (erased ct))
    (fp-concat-unassoc _ prefix middle after rest oe cr ca))
  (let ((erased suffix) (erased cs) (erased out))
    (fp-concat-assoc _ end after oe ot xs ct oc2))
  (MkPalRange xs prefix middle end suffix newlo width newhi ce out
    (fp-concat-length _ op before prefix lo cut newlo cp olp lb al)
    lm size))

(def-adts $ (PalCut : ((List (Nat)) xs) ((Nat) i) ((List (Nat)) left right) -> Type)
  enum
  (many MkPalCut : (erased (List (Nat)) xs prefix left right) (erased (Nat) i)
    (erased (PalConcat (Nat) prefix right xs) cat)
    (erased (Reverse (Nat) prefix left) rev)
    (erased (PalLength (Nat) prefix i) len) -> (PalCut xs i left right)))

(def-fns _ $ (erased fp-cut-unique : (erased (List (Nat)) xs l1 r1 l2 r2)
    (erased (Nat) i) (erased (PalCut xs i l1 r1) p) (erased (PalCut xs i l2 r2) q) ->
    (erased (Eq (List (Nat)) l1 l2) el) (erased (Eq (List (Nat)) r1 r2) er))
  (let-match erased p (MkPalCut source prefix left right j cat rev len))
  (let-match erased q (MkPalCut source2 prefix2 left2 right2 j2 cat2 rev2 len2))
  (let ((erased ep) (erased er))
    (fp-split-unique _ xs prefix r1 prefix2 r2 i cat cat2 len len2))
  (let-match erased ep (Refl t v))
  (values (fp-reverse-unique _ prefix l1 l2 rev rev2) er))

; A palindrome whose left margin is k before this center supplies k known
; matches to its two outward-facing lists. The tails are returned erased;
; certified context lookups reify them without walking the skipped prefix.
(def-fns _ $ (erased fp-center-seed :
    (erased (List (Nat)) xs left fullright right actualmid w)
    (erased (Nat) i lo hi k d extra width)
    (erased (PalSplit xs left fullright) split) (erased (PalLength (Nat) left i) llen)
    (erased (PalLength (Nat) actualmid extra) mlen)
    (erased (PalConcat (Nat) actualmid right fullright) mcat)
    (erased (PalRange xs lo hi w) range) (erased (Palindrome (Nat) w) pal)
    (erased (PalLength (Nat) w width) len)
    (erased (Double k d) twice) (erased (Add d extra width) count)
    (erased (PalParity extra) parity) (erased (Add lo k i) offset) ->
    (erased (List (Nat)) common lrest rrest)
    (erased (PalConcat (Nat) common lrest left) cl)
    (erased (PalConcat (Nat) common rrest right) cr)
    (erased (PalLength (Nat) common k) lc)
    (erased (List (Nat)) loRight hiLeft)
    (erased (PalCut xs lo lrest loRight) lowcut)
    (erased (PalCut xs hi hiLeft rrest) highcut))
  (let ((erased lh) (erased mid) (erased rh) (erased mr)
       (erased catleft) (erased catright) (erased ll) (erased lr) (erased lm) (erased rev))
    (fp-pal-halves w k d extra width pal len twice count parity))
  (let ((erased prefix0) (erased cat0) (erased rev0))
    (fp-split-decomp xs left fullright split))
  (let ((erased lp0))
    (fp-reverse-length _ left prefix0 i (fp-reverse-involutive _ prefix0 left rev0) llen))
  (let-match erased range (MkPalRange source op ow oe ot ol on oh oc1 oc2 olp olw osum))
  (let ((erased prefix) (erased cp) (erased ct))
    (fp-concat-unassoc _ op lh mr w oe oc1 catleft))
  (let ((erased rest0) (erased cr0) (erased cwhole))
    (fp-concat-assoc _ prefix mr oe ot xs ct oc2))
  (let ((erased lp))
    (fp-concat-length _ op lh prefix lo k i cp olp ll offset))
  (let ((erased ep) (erased er))
    (fp-split-unique _ xs prefix rest0 prefix0 fullright i cwhole cat0 lp lp0))
  (let-match erased ep (Refl t v))
  (let-match erased er (Refl t3 v2))
  (let ((erased rrest0) (erased cright) (erased cmid))
    (fp-concat-assoc _ mid rh mr ot fullright catright cr0))
  (let ((erased em) (erased ert))
    (fp-split-unique _ fullright mid rrest0 actualmid right extra cmid mcat lm mlen))
  (let-match erased ert (Refl t3b v2b))
  (let ((erased rp) (erased rproof)) (fp-reverse _ op))
  (let ((erased rprefix) (erased rpreproof) (erased cl))
    (fp-reverse-concat _ op lh prefix rp rh cp rproof rev))
  (let-match erased (fp-reverse-unique _ prefix rprefix left rpreproof rev0) (Refl t3b2 v2b2))
  (let ((erased loRight) (erased lowrest) (erased lowcat))
    (fp-concat-assoc _ op w oe ot xs oc1 oc2))
  (let ((erased hiLeft) (erased highrev)) (fp-reverse _ oe))
  (values rh rp ot cl cright lr loRight hiLeft
    (MkPalCut xs op rp loRight lo lowcat rproof olp)
    (MkPalCut xs oe hiLeft ot hi oc2 highrev
      (fp-concat-length _ op w oe lo on hi oc1 olp olw osum))))

; Add a known matching prefix to the result of expanding its tails.
(def-fns _ $ (erased fp-lcp-prepend :
    (subterm erased (List (Nat)) common) (erased (List (Nat)) lrest rrest left right)
    (erased (Nat) k tailn n)
    (erased (PalConcat (Nat) common lrest left) cl)
    (erased (PalConcat (Nat) common rrest right) cr)
    (erased (PalLength (Nat) common k) len)
    (erased (PalLcp lrest rrest tailn) p) (erased (Add k tailn n) sum) ->
    (erased (PalLcp left right n) out))
  (match erased common _
    ((Nil a)
      (let-match erased len (PalLNil b))
      (let-match erased cl (PalCatNil c left0))
      (let-match erased cr (PalCatNil d right0))
      (let-match erased sum (AddZero v))
      p)
    ((Cons a x rest)
      (let-match erased len (PalLCons b y rest2 k1 len1))
      (let-match erased cl (PalCatCons c z rest3 tail3 out cl1))
      (let-match erased cr (PalCatCons d z2 rest4 tail2 out2 cr1))
      (let-match erased sum (AddSucc a1 b1 c1 sum1))
      (PLStep x _ _ _
        (fp-lcp-prepend rest lrest rrest out out2 k1 tailn c1 cl1 cr1 len1 p sum1)))))

; Reconstruct a located palindrome from a center's exact expansion proof.
(def-fns _ $ (erased fp-center-range-base :
    (erased (List (Nat)) xs left right mid full) (erased (Nat) m n)
    (erased (PalSplit xs left full) split) (erased (Palindrome (Nat) mid) pal)
    (erased (PalLength (Nat) mid m) len) (erased (PalConcat (Nat) mid right full) cat)
    (erased (Add (Zero) m n) sum) (erased (Nat) leftn lo hi)
    (erased (PalLength (Nat) left leftn) llen) (erased (Add (Zero) lo leftn) offset)
    (erased (Add lo n hi) endpoint) ->
    (erased (List (Nat)) w) (erased (PalRange xs lo hi w) range)
    (erased (Palindrome (Nat) w) proof) (erased (PalLength (Nat) w n) wlen))
  (let-match erased sum (AddZero v))
  (let-match erased offset (AddZero v2))
  (let ((erased prefix) (erased cp) (erased rev)) (fp-split-decomp xs left full split))
  (let ((erased plen)) (fp-reverse-length _ left prefix lo
    (fp-reverse-involutive _ prefix left rev) llen))
  (let ((erased end) (erased ce) (erased ct))
    (fp-concat-unassoc _ prefix mid right full xs cp cat))
  (values mid (MkPalRange xs prefix mid end right lo n hi ce ct plen len endpoint)
    pal len))

(def-fns _ $ (erased fp-center-range : (erased (List (Nat)) xs left right)
    (erased (Nat) k d) (subterm erased (PalLcp left right k) common)
    (erased (Double k d) twice)
    (erased (List (Nat)) mid full) (erased (Nat) m n)
    (erased (PalSplit xs left full) split) (erased (Palindrome (Nat) mid) pal)
    (erased (PalLength (Nat) mid m) len) (erased (PalConcat (Nat) mid right full) cat)
    (erased (Add d m n) sum)
    (erased (Nat) leftn lo hi) (erased (PalLength (Nat) left leftn) llen)
    (erased (Add k lo leftn) offset) (erased (Add lo n hi) endpoint) ->
    (erased (List (Nat)) w) (erased (PalRange xs lo hi w) range)
    (erased (Palindrome (Nat) w) proof) (erased (PalLength (Nat) w n) wlen))
  (match erased common _
    ((PLLeft r)
      (let-match erased twice (D0))
      (fp-center-range-base xs left right mid full m n split pal len cat sum leftn lo hi llen offset endpoint))
    ((PLRight l)
      (let-match erased twice (D0))
      (fp-center-range-base xs left right mid full m n split pal len cat sum leftn lo hi llen offset endpoint))
    ((PLApart x y l r apart)
      (let-match erased twice (D0))
      (fp-center-range-base xs left right mid full m n split pal len cat sum leftn lo hi llen offset endpoint))
    ((PLStep x l r k1 p)
      (let-match erased split (PSStep source l2 full2 y split1))
      (let-match erased llen (PalLCons a0 x0 l0 ln llen1))
      (let-match erased offset (AddSucc k0 lo0 ln0 offset1))
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
      (fp-center-range xs l r k1 d1 p twice1
        (Cons _ x withx) (Cons _ x full) (Succ (Succ m)) n
        split1 (PalWrap _ x _ _ pal snoc)
        (PalLCons _ x _ _ withxlen)
        (PalCatCons _ x _ _ _ restcat)
        (add-succ-right d1 _ _
          (add-succ-right d1 m c2 sum2))
        ln lo hi llen1 offset1 endpoint))))


(def-fns _ $ (erased fp-lcp-bound : (erased (List (Nat)) left right)
    (erased (Nat) k n) (subterm erased (PalLcp left right k) p)
    (erased (PalLength (Nat) left n) len) -> (erased (Lt k (Succ n)) bound))
  (match erased p _
    ((PLLeft r) (LtZ n))
    ((PLRight l) (LtZ n))
    ((PLApart x y l r apart) (LtZ n))
    ((PLStep x l r k1 p1)
      (let-match erased len (PalLCons a y rest n1 len1))
      (LtS _ _ (fp-lcp-bound l r k1 n1 p1 len1)))))

(def-fns _ $ (erased fp-cut-step : (erased (List (Nat)) xs left right)
    (erased (Nat) i x) (erased (PalCut xs i left (Cons (Nat) x right)) cut) ->
    (erased (PalCut xs (Succ i) (Cons (Nat) x left) right) next))
  (let-match erased cut (MkPalCut source prefix l r j cat rev len))
  (let ((erased out) (erased snoc) (erased final))
    (fp-concat-unassoc _ prefix _ right
      _ xs cat
      (PalCatCons _ x _ _ _ (PalCatNil _ right))))
  (MkPalCut xs out _ right _ final
    (fp-reverse-snoc _ prefix left out x rev snoc)
    (fp-concat-length _ prefix _ out i (Succ (Zero))
      _ snoc len (PalLCons _ x _ _ (PalLNil _))
      (add-succ-right i (Zero) i (add-zero-right i)))))
