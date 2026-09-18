; The positive certificates used when Manacher starts expansion at a reused
; mirror radius. Depends on palindrome_lemmas.sl and palindrome_centers.sl.

(def-adts $ PalParity : ((Nat) extra) -> Type enum
  (many PPEven : -> (PalParity (Zero)))
  (many PPOdd : -> (PalParity (Succ (Zero)))))

(def-fns _ $ erased fp-split-decomp : (erased (List (Nat)) xs left right)
    (subterm erased (PalSplit xs left right) split) ->
    (erased (List (Nat)) prefix)
    (erased (Concat (Nat) prefix right xs) cat)
    (erased (Reverse (Nat) prefix left) rev)
  (match erased split _
    ((PSStart source) (values (Nil (Nat)) (CatNil (Nat) xs) (RevNil (Nat))))
    ((PSStep source l r x p)
      (let (erased prefix) (erased cat) (erased rev)
        (fp-split-decomp xs l (Cons (Nat) x right) p))
      (let (erased out) (erased snoc) (erased final)
        (fp-concat-unassoc (Nat) prefix (Cons (Nat) x (Nil (Nat))) right
          (Cons (Nat) x right) xs cat
          (CatCons (Nat) x (Nil (Nat)) right right (CatNil (Nat) right))))
      (values out final (fp-reverse-snoc (Nat) prefix l out x rev snoc)))))

(def-fns _ $ erased fp-reverse-involutive : (erased Type A)
    (erased (List A) xs ys) (subterm erased (Reverse A xs ys) rev) ->
    (erased (Reverse A ys xs) back)
  (match erased rev _
    ((RevNil a) (RevNil A))
    ((RevCons a x rest tail out p q)
      (fp-reverse-snoc A tail rest ys x (fp-reverse-involutive A rest tail p) q))))

; Split a palindrome into equal-length reversed halves and a 0/1-element middle.
(def-fns _ $ erased fp-pal-halves : (erased (List (Nat)) w)
    (erased (Nat) k d extra width)
    (subterm erased (Palindrome (Nat) w) pal)
    (erased (Length (Nat) w width) len)
    (erased (Double k d) twice) (erased (Add d extra width) sum)
    (erased (PalParity extra) parity) ->
    (erased (List (Nat)) lh mid rh mr)
    (erased (Concat (Nat) lh mr w) catleft)
    (erased (Concat (Nat) mid rh mr) catright)
    (erased (Length (Nat) lh k) ll) (erased (Length (Nat) rh k) lr)
    (erased (Length (Nat) mid extra) lm)
    (erased (Reverse (Nat) lh rh) rev)
  (match erased pal _
    ((PalNil a)
      (match erased len _
        ((LNil b)
          (match erased sum _
            ((AddZero v)
              (match erased twice _
                ((D0) (values (Nil (Nat)) (Nil (Nat)) (Nil (Nat)) (Nil (Nat))
                  (CatNil (Nat) (Nil (Nat))) (CatNil (Nat) (Nil (Nat)))
                  (LNil (Nat)) (LNil (Nat)) (LNil (Nat)) (RevNil (Nat))))))))))
    ((PalOne a x)
      (match erased len _
        ((LCons b y rest j lp)
          (match erased lp _
            ((LNil c)
              (match erased twice _
                ((D0)
                  (match erased sum _
                    ((AddZero v)
                      (values (Nil (Nat)) w (Nil (Nat)) w
                        (CatNil (Nat) w) (fp-concat-nil (Nat) w)
                        (LNil (Nat)) (LNil (Nat)) len (RevNil (Nat))))))
                (absurd (DS a2 b2 p)
                  (match erased sum (((False) f))
                    ((AddSucc a3 b3 c3 p3) (match erased p3 _))))))))))
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
          (match erased twice _
            (absurd (D0)
              (match erased sum (((False) f)) ((AddZero v) (match erased parity _))))
            ((DS k1 d1 twice1)
              (match erased sum _
                ((AddSucc a1 b1 c1 sum1)
                  (match erased sum1 _
                    ((AddSucc a2 b2 c2 sum2)
                      (let (erased lh) (erased mid) (erased rh) (erased mr)
                           (erased cl) (erased cr) (erased ll) (erased lr) (erased lm) (erased rev)
                        (fp-pal-halves inner k1 d1 extra ni innerpal li twice1 sum2 parity))
                      (let (erased mr2) (erased mrSnoc) (erased cl2)
                        (fp-concat-assoc (Nat) lh mr inner (Cons (Nat) x (Nil (Nat))) withx cl snoc))
                      (let (erased rh2) (erased rhSnoc) (erased cr2)
                        (fp-concat-assoc (Nat) mid rh mr (Cons (Nat) x (Nil (Nat))) mr2 cr mrSnoc))
                      (values (Cons (Nat) x lh) mid rh2 mr2
                        (CatCons (Nat) x lh mr2 withx cl2) cr2
                        (LCons (Nat) x lh k1 ll)
                        (fp-concat-length (Nat) rh (Cons (Nat) x (Nil (Nat))) rh2
                          k1 (Succ (Zero)) (Succ k1) rhSnoc lr
                          (LCons (Nat) x (Nil (Nat)) (Zero) (LNil (Nat)))
                          (add-succ-right k1 (Zero) k1 (add-zero-right k1)))
                        lm (RevCons (Nat) x lh rh rh2 rev rhSnoc)))))))))))))

; Remove the same number of elements from both ends of a palindrome.
; sum states that the two removed margins and the desired middle exhaust it.
(def-fns _ $ erased fp-pal-trim : (erased (List (Nat)) w)
    (subterm erased (Nat) cut) (erased (Nat) dc target width)
    (erased (Palindrome (Nat) w) pal) (erased (Length (Nat) w width) len)
    (erased (Double cut dc) twice) (erased (Add dc target width) sum) ->
    (erased (List (Nat)) before middle after rest)
    (erased (Concat (Nat) before rest w) cb)
    (erased (Concat (Nat) middle after rest) ca)
    (erased (Length (Nat) before cut) lb) (erased (Length (Nat) after cut) la)
    (erased (Length (Nat) middle target) lm) (erased (Palindrome (Nat) middle) pm)
  (match erased cut _
    ((Zero)
      (match erased twice _
        ((D0)
          (match erased sum _
            ((AddZero v)
              (values (Nil (Nat)) w (Nil (Nat)) w
                (CatNil (Nat) w) (fp-concat-nil (Nat) w)
                (LNil (Nat)) (LNil (Nat)) len pal))))))
    ((Succ c)
      (match erased twice _
        ((DS c1 d1 twice1)
          (match erased sum _
            ((AddSucc a b s sum1)
              (match erased sum1 _
                ((AddSucc a2 b2 s2 sum2)
                  (match erased pal _
                    (absurd (PalNil t) (match erased len (((False) f))))
                    (absurd (PalOne t x)
                      (match erased len (((False) f))
                        ((LCons t2 x2 rest k p) (match erased p _))))
                    ((PalWrap t x inner withx pi snoc)
                      (let (erased ni) (erased li) (pal-length inner))
                      (let (erased lwith)
                        (fp-concat-length (Nat) inner (Cons (Nat) x (Nil (Nat))) withx
                          ni (Succ (Zero)) (Succ ni) snoc li
                          (LCons (Nat) x (Nil (Nat)) (Zero) (LNil (Nat)))
                          (add-succ-right ni (Zero) ni (add-zero-right ni))))
                      (match erased (fp-length-unique (Nat) w width (Succ (Succ ni)) len
                                      (LCons (Nat) x withx (Succ ni) lwith)) _
                        ((Refl t v)
                          (let (erased before) (erased middle) (erased after) (erased rest)
                               (erased cb) (erased ca) (erased lb) (erased la) (erased lm) (erased pm)
                            (fp-pal-trim inner c d1 target ni pi li twice1 sum2))
                          (let (erased rest2) (erased restSnoc) (erased cb2)
                            (fp-concat-assoc (Nat) before rest inner (Cons (Nat) x (Nil (Nat))) withx cb snoc))
                          (let (erased after2) (erased afterSnoc) (erased ca2)
                            (fp-concat-assoc (Nat) middle after rest (Cons (Nat) x (Nil (Nat))) rest2 ca restSnoc))
                          (values (Cons (Nat) x before) middle after2 rest2
                            (CatCons (Nat) x before rest2 withx cb2) ca2
                            (LCons (Nat) x before c lb)
                            (fp-concat-length (Nat) after (Cons (Nat) x (Nil (Nat))) after2
                              c (Succ (Zero)) (Succ c) afterSnoc la
                              (LCons (Nat) x (Nil (Nat)) (Zero) (LNil (Nat)))
                              (add-succ-right c (Zero) c (add-zero-right c))) lm pm))))))))))))))

(def-fns _ $ erased fp-concat-add : (erased Type A)
    (erased (List A) xs ys zs) (erased (Nat) n m k)
    (subterm erased (Concat A xs ys zs) cat)
    (erased (Length A xs n) lx) (erased (Length A ys m) ly)
    (erased (Length A zs k) lz) -> (erased (Add n m k) sum)
  (match erased cat _
    ((CatNil a tail)
      (match erased lx _
        ((LNil b)
          (match erased (fp-length-unique A ys m k ly lz) _
            ((Refl t v) (AddZero m))))))
    ((CatCons a x rest tail out cat1)
      (match erased lx _
        ((LCons b y rest2 n1 lx1)
          (match erased lz _
            ((LCons c z out2 k1 lz1)
              (AddSucc n1 m k1 (fp-concat-add A rest ys out n1 m k1 cat1 lx1 ly lz1)))))))))

(def-fns _ $ erased fp-add-cancel-right : (erased (Nat) a b c total)
    (erased (Add a c total) p) (erased (Add b c total) q) ->
    (erased (Eq (Nat) a b) same)
  (fp-add-cancel-left c a b total (add-comm a c total p) (add-comm b c total q)))

; Put a trimmed decomposition back into the original input's coordinates.
(def-fns _ $ erased fp-trim-range : (erased (List (Nat)) xs w before middle after rest)
    (erased (Nat) lo hi cut newlo newhi width)
    (erased (PalRange xs lo hi w) range)
    (erased (Concat (Nat) before rest w) cb)
    (erased (Concat (Nat) middle after rest) ca)
    (erased (Length (Nat) before cut) lb) (erased (Length (Nat) after cut) la)
    (erased (Length (Nat) middle width) lm)
    (erased (Add lo cut newlo) al) (erased (Add newhi cut hi) ah)
    (erased (Add newlo width newhi) size) ->
    (erased (PalRange xs newlo newhi middle) out)
  (match erased range _
    ((MkPalRange source op ow oe ot ol on oh oc1 oc2 olp olw osum)
      (let (erased prefix) (erased cp) (erased cr)
        (fp-concat-unassoc (Nat) op before rest w oe oc1 cb))
      (let (erased end) (erased ce) (erased ct)
        (fp-concat-unassoc (Nat) prefix middle after rest oe cr ca))
      (let (erased suffix) (erased cs) (erased out)
        (fp-concat-assoc (Nat) end after oe ot xs ct oc2))
      (MkPalRange xs prefix middle end suffix newlo width newhi ce out
        (fp-concat-length (Nat) op before prefix lo cut newlo cp olp lb al)
        lm size))))

(def-adts $ PalCut : ((List (Nat)) xs) ((Nat) i) ((List (Nat)) left right) -> Type
  enum
  (many MkPalCut : (erased (List (Nat)) xs prefix left right) (erased (Nat) i)
    (erased (Concat (Nat) prefix right xs) cat)
    (erased (Reverse (Nat) prefix left) rev)
    (erased (Length (Nat) prefix i) len) -> (PalCut xs i left right)))

(def-fns _ $ erased fp-cut-unique : (erased (List (Nat)) xs l1 r1 l2 r2)
    (erased (Nat) i) (erased (PalCut xs i l1 r1) p) (erased (PalCut xs i l2 r2) q) ->
    (erased (Eq (List (Nat)) l1 l2) el) (erased (Eq (List (Nat)) r1 r2) er)
  (match erased p _
    ((MkPalCut source prefix left right j cat rev len)
      (match erased q _
        ((MkPalCut source2 prefix2 left2 right2 j2 cat2 rev2 len2)
          (let (erased ep) (erased er)
            (fp-split-unique (Nat) xs prefix r1 prefix2 r2 i cat cat2 len len2))
          (match erased ep _
            ((Refl t v) (values (fp-reverse-unique (Nat) prefix l1 l2 rev rev2) er))))))))

; A palindrome whose left margin is k before this center supplies k known
; matches to its two outward-facing lists. The tails are returned erased;
; certified context lookups reify them without walking the skipped prefix.
(def-fns _ $ erased fp-center-seed :
    (erased (List (Nat)) xs left fullright right actualmid w)
    (erased (Nat) i lo hi k d extra width)
    (erased (PalSplit xs left fullright) split) (erased (Length (Nat) left i) llen)
    (erased (Length (Nat) actualmid extra) mlen)
    (erased (Concat (Nat) actualmid right fullright) mcat)
    (erased (PalRange xs lo hi w) range) (erased (Palindrome (Nat) w) pal)
    (erased (Length (Nat) w width) len)
    (erased (Double k d) twice) (erased (Add d extra width) count)
    (erased (PalParity extra) parity) (erased (Add lo k i) offset) ->
    (erased (List (Nat)) common lrest rrest)
    (erased (Concat (Nat) common lrest left) cl)
    (erased (Concat (Nat) common rrest right) cr)
    (erased (Length (Nat) common k) lc)
    (erased (List (Nat)) loRight hiLeft)
    (erased (PalCut xs lo lrest loRight) lowcut)
    (erased (PalCut xs hi hiLeft rrest) highcut)
  (let (erased lh) (erased mid) (erased rh) (erased mr)
       (erased catleft) (erased catright) (erased ll) (erased lr) (erased lm) (erased rev)
    (fp-pal-halves w k d extra width pal len twice count parity))
  (let (erased prefix0) (erased cat0) (erased rev0)
    (fp-split-decomp xs left fullright split))
  (let (erased lp0)
    (fp-reverse-length (Nat) left prefix0 i (fp-reverse-involutive (Nat) prefix0 left rev0) llen))
  (match erased range _
    ((MkPalRange source op ow oe ot ol on oh oc1 oc2 olp olw osum)
      (let (erased prefix) (erased cp) (erased ct)
        (fp-concat-unassoc (Nat) op lh mr w oe oc1 catleft))
      (let (erased rest0) (erased cr0) (erased cwhole)
        (fp-concat-assoc (Nat) prefix mr oe ot xs ct oc2))
      (let (erased lp)
        (fp-concat-length (Nat) op lh prefix lo k i cp olp ll offset))
      (let (erased ep) (erased er)
        (fp-split-unique (Nat) xs prefix rest0 prefix0 fullright i cwhole cat0 lp lp0))
      (match erased ep _
        ((Refl t v)
          (match erased er _
            ((Refl t v)
              (let (erased rrest0) (erased cright) (erased cmid)
                (fp-concat-assoc (Nat) mid rh mr ot fullright catright cr0))
              (let (erased em) (erased ert)
                (fp-split-unique (Nat) fullright mid rrest0 actualmid right extra cmid mcat lm mlen))
              (match erased ert _
                ((Refl t v)
                  (let (erased rp) (erased rproof) (fp-reverse (Nat) op))
                  (let (erased rprefix) (erased rpreproof) (erased cl)
                    (fp-reverse-concat (Nat) op lh prefix rp rh cp rproof rev))
                  (match erased (fp-reverse-unique (Nat) prefix rprefix left rpreproof rev0) _
                    ((Refl t v)
                      (let (erased loRight) (erased lowrest) (erased lowcat)
                        (fp-concat-assoc (Nat) op w oe ot xs oc1 oc2))
                      (let (erased hiLeft) (erased highrev) (fp-reverse (Nat) oe))
                      (values rh rp ot cl cright lr loRight hiLeft
                        (MkPalCut xs op rp loRight lo lowcat rproof olp)
                        (MkPalCut xs oe hiLeft ot hi oc2 highrev
                          (fp-concat-length (Nat) op w oe lo on hi oc1 olp olw osum))))))))))))))

; Add a known matching prefix to the result of expanding its tails.
(def-fns _ $ erased fp-lcp-prepend :
    (subterm erased (List (Nat)) common) (erased (List (Nat)) lrest rrest left right)
    (erased (Nat) k tailn n)
    (erased (Concat (Nat) common lrest left) cl)
    (erased (Concat (Nat) common rrest right) cr)
    (erased (Length (Nat) common k) len)
    (erased (PalLcp lrest rrest tailn) p) (erased (Add k tailn n) sum) ->
    (erased (PalLcp left right n) out)
  (match erased common _
    ((Nil a)
      (match erased len _
        ((LNil b)
          (match erased cl _
            ((CatNil c left0)
              (match erased cr _
                ((CatNil d right0) (match erased sum _ ((AddZero v) p)))))))))
    ((Cons a x rest)
      (match erased len _
        ((LCons b y rest2 k1 len1)
          (match erased cl _
            ((CatCons c z rest3 tail out cl1)
              (match erased cr _
                ((CatCons d z2 rest4 tail2 out2 cr1)
                  (match erased sum _
                    ((AddSucc a1 b1 c1 sum1)
                      (PLStep x out out2 c1
                        (fp-lcp-prepend rest lrest rrest out out2 k1 tailn c1 cl1 cr1 len1 p sum1)))))))))))))

; Reconstruct a located palindrome from a center's exact expansion proof.
(def-fns _ $ erased fp-center-range-base :
    (erased (List (Nat)) xs left right mid full) (erased (Nat) m n)
    (erased (PalSplit xs left full) split) (erased (Palindrome (Nat) mid) pal)
    (erased (Length (Nat) mid m) len) (erased (Concat (Nat) mid right full) cat)
    (erased (Add (Zero) m n) sum) (erased (Nat) leftn lo hi)
    (erased (Length (Nat) left leftn) llen) (erased (Add (Zero) lo leftn) offset)
    (erased (Add lo n hi) endpoint) ->
    (erased (List (Nat)) w) (erased (PalRange xs lo hi w) range)
    (erased (Palindrome (Nat) w) proof) (erased (Length (Nat) w n) length)
  (match erased sum _
    ((AddZero v)
      (match erased offset _
        ((AddZero v)
          (let (erased prefix) (erased cp) (erased rev) (fp-split-decomp xs left full split))
          (let (erased plen) (fp-reverse-length (Nat) left prefix lo
            (fp-reverse-involutive (Nat) prefix left rev) llen))
          (let (erased end) (erased ce) (erased ct)
            (fp-concat-unassoc (Nat) prefix mid right full xs cp cat))
          (values mid (MkPalRange xs prefix mid end right lo n hi ce ct plen len endpoint)
            pal len))))))

(def-fns _ $ erased fp-center-range : (erased (List (Nat)) xs left right)
    (erased (Nat) k d) (subterm erased (PalLcp left right k) common)
    (erased (Double k d) twice)
    (erased (List (Nat)) mid full) (erased (Nat) m n)
    (erased (PalSplit xs left full) split) (erased (Palindrome (Nat) mid) pal)
    (erased (Length (Nat) mid m) len) (erased (Concat (Nat) mid right full) cat)
    (erased (Add d m n) sum)
    (erased (Nat) leftn lo hi) (erased (Length (Nat) left leftn) llen)
    (erased (Add k lo leftn) offset) (erased (Add lo n hi) endpoint) ->
    (erased (List (Nat)) w) (erased (PalRange xs lo hi w) range)
    (erased (Palindrome (Nat) w) proof) (erased (Length (Nat) w n) length)
  (match erased common _
    ((PLLeft r)
      (match erased twice _
        ((D0) (fp-center-range-base xs left right mid full m n split pal len cat sum leftn lo hi llen offset endpoint))))
    ((PLRight l)
      (match erased twice _
        ((D0) (fp-center-range-base xs left right mid full m n split pal len cat sum leftn lo hi llen offset endpoint))))
    ((PLApart x y l r apart)
      (match erased twice _
        ((D0) (fp-center-range-base xs left right mid full m n split pal len cat sum leftn lo hi llen offset endpoint))))
    ((PLStep x l r k1 p)
      (match erased split _
        ((PSStep source l2 full2 y split1)
          (match erased llen _
            ((LCons a0 x0 l0 ln llen1)
              (match erased offset _
                ((AddSucc k0 lo0 ln0 offset1)
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
                              (fp-center-range xs l r k1 d1 p twice1
                                (Cons (Nat) x withx) (Cons (Nat) x full) (Succ (Succ m)) n
                                split1 (PalWrap (Nat) x mid withx pal snoc)
                                (LCons (Nat) x withx (Succ m) withxlen)
                                (CatCons (Nat) x withx r full restcat)
                                (add-succ-right d1 (Succ m) (Succ c2)
                                  (add-succ-right d1 m c2 sum2))
                                ln lo hi llen1 offset1 endpoint))))))))))))))))


(def-fns _ $ erased fp-lcp-bound : (erased (List (Nat)) left right)
    (erased (Nat) k n) (subterm erased (PalLcp left right k) p)
    (erased (Length (Nat) left n) len) -> (erased (Lt k (Succ n)) bound)
  (match erased p _
    ((PLLeft r) (LtZ n))
    ((PLRight l) (LtZ n))
    ((PLApart x y l r apart) (LtZ n))
    ((PLStep x l r k1 p1)
      (match erased len _
        ((LCons a y rest n1 len1)
          (LtS k1 (Succ n1) (fp-lcp-bound l r k1 n1 p1 len1)))))))

(def-fns _ $ erased fp-cut-step : (erased (List (Nat)) xs left right)
    (erased (Nat) i x) (erased (PalCut xs i left (Cons (Nat) x right)) cut) ->
    (erased (PalCut xs (Succ i) (Cons (Nat) x left) right) next)
  (match erased cut _
    ((MkPalCut source prefix l r j cat rev len)
      (let (erased out) (erased snoc) (erased final)
        (fp-concat-unassoc (Nat) prefix (Cons (Nat) x (Nil (Nat))) right
          (Cons (Nat) x right) xs cat
          (CatCons (Nat) x (Nil (Nat)) right right (CatNil (Nat) right))))
      (MkPalCut xs out (Cons (Nat) x left) right (Succ i) final
        (fp-reverse-snoc (Nat) prefix left out x rev snoc)
        (fp-concat-length (Nat) prefix (Cons (Nat) x (Nil (Nat))) out i (Succ (Zero))
          (Succ i) snoc len (LCons (Nat) x (Nil (Nat)) (Zero) (LNil (Nat)))
          (add-succ-right i (Zero) i (add-zero-right i)))))))
