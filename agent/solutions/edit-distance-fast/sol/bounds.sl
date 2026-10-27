; Distance bounds, independent of any implementation of the dynamic program.
(def-fns _ $ (erased ed-le-trans : (erased (Nat) a b c) (erased (NatLe a b) ab) (erased (NatLe b c) bc) ->
    (erased (NatLe a c) ac))
  (MkNatLe a c (lt-le-trans a (Succ b) (Succ c) (le-lt a b ab) (LtS b (Succ c) (le-lt b c bc)))))

(def-fns _ $ (erased ed-atmost-member : (erased (Nat) d) (erased (List (Nat)) cs)
    (erased (AtMost d cs) p) (erased (Nat) i c) (subterm erased (Nth (Nat) cs i c) member) -> (erased (NatLe d c) q))
  (let-match erased member (NthThere _ _ rest j _ more)
    ((NthHere _ _ _) (let-match erased p (AtMostCons _ _ _ q _)) q))
  (let-match erased p (AtMostCons _ _ _ _ ys1))
  (ed-atmost-member d rest ys1 j c more))

(def-fns _ $ (erased ed-least-member : (erased (List (Nat)) cs) (erased (Nat) d)
    (erased (Least cs d) least) (erased (Nat) i c) (erased (Nth (Nat) cs i c) member) -> (erased (NatLe d c) q))
  (let-match erased least (MkLeast _ _ _ _ below))
  (ed-atmost-member d cs below i c member))

(def-fns _ $ (erased ed-add2-le : (erased (Nat) a d b) (erased (Add 2 a d) sum) (erased (NatLe a b) ab) ->
    (erased (NatLe d (Succ (Succ b))) q))
  (let-match erased sum (AddSucc _ _ _ sum1))
  (let-match erased sum1 (AddSucc _ _ _ sum0))
  (let-match erased sum0 (AddZero _))
  (MkNatLe _ _ (LtS _ _ (LtS _ _ (le-lt a b ab)))))

; The deletion candidate alone suffices in DistStep. This proof does not
; recurse into substitution, insertion or Swap; proof-size growth is linear
; in the two lengths, even if Dist has an enormous recurrence tree.
(def-fns _ $ (erased ed-dist-bound : (erased (List (U8)) xs ys) (erased (Nat) d)
    (subterm erased (Dist xs ys d) dist) (erased (Nat) nx ny total upper)
    (erased (Length (U8) xs nx) lx) (erased (Length (U8) ys ny) ly)
    (erased (Add nx ny total) sum) (erased (Double total upper) twice) -> (erased (NatLe d upper) bound))
  (match erased dist _
    ((DistNil)
      (let-match erased lx (LengthNil _))
      (let-match erased ly (LengthNil _))
      (let-match erased sum (AddZero _))
      (let-match erased twice (D0))
      (MkNatLe 0 0 (lt-succ 0)))
    ((DistDelete _ rest a da _ add2)
      (let-match erased lx (LengthCons _ _ _ n1 lx1))
      (let-match erased ly (LengthNil _))
      (let-match erased sum (AddSucc _ _ total1 sum1))
      (let-match erased twice (DS _ upper1 twice1))
      (ed-add2-le a d upper1 add2
        (ed-dist-bound rest (Nil _) a da n1 0 total1 upper1 lx1 (LengthNil _) sum1 twice1)))
    ((DistInsert _ rest a da _ add2)
      (let-match erased lx (LengthNil _))
      (let-match erased ly (LengthCons _ _ _ n1 ly1))
      (let-match erased sum (AddZero _))
      (let-match erased twice (DS _ upper1 twice1))
      (ed-add2-le a d upper1 add2
        (ed-dist-bound (Nil _) rest a da 0 n1 n1 upper1 (LengthNil _) ly1 (AddZero n1) twice1)))
    ((DistStep _ rest y ys1 _ _ _ _ s _ b db t tb _ _ _ _ _ _ _ least)
      (let-match erased lx (LengthCons _ _ _ n1 lx1))
      (let-match erased sum (AddSucc _ _ total1 sum1))
      (let-match erased twice (DS _ upper1 twice1))
      (ed-le-trans d t upper
        (ed-least-member _ d least 1 t (NthThere _ s _ 0 t (NthHere _ t _)))
        (ed-add2-le b t upper1 tb
          (ed-dist-bound rest (Cons _ y ys1) b db n1 ny total1 upper1 lx1 ly sum1 twice1))))))

; Binary numeral certificates expose a doubling in constant-sized source.
(unary 18014398509481984 18014398509481983)
(unary 36028797018963968 36028797018963967)
(let-match erased (numeral-of 36028797018963968) (N2 ed-max-bin ed-max-minus1 ed-max-double-minus2 ed-max-num ed-max-dd))
(let-match erased (numeral-fn _ _ _ ed-max-num (numeral-of 18014398509481983)) (Refl _ _))
(let ((erased (Double max-array-length 36028797018963968) ed-max-double))
  (DS _ _ ed-max-dd))
(let-match erased (numeral-of 72057594037927936) (N2 ed-max2-bin ed-max2-minus1 ed-max2-double-minus2 ed-max2-num ed-max2-dd))
(let-match erased (numeral-fn _ _ _ ed-max2-num (numeral-of 36028797018963967)) (Refl _ _))
(let ((erased (Double 36028797018963968 72057594037927936) ed-max2-double))
  (DS _ _ ed-max2-dd))
(let ((erased ed-max4-small)) (prove-literal-lt 72057594037927936 1152921504606846976))

(def-fns _ $ (erased ed-length-sum-small : (erased (Nat) nx ny total upper)
    (erased (Lt nx max-array-length) px) (erased (Lt ny max-array-length) py)
    (erased (Add nx ny total) sum) (erased (Double total upper) twice) -> (erased (Lt upper ed-value-limit) fits))
  (let ((erased z) (erased x-max)) (add nx max-array-length))
  (let ((erased tz)) (ed-add-mono nx ny max-array-length total z sum x-max py))
  (let ((erased z-max2))
    (ed-add-mono max-array-length nx max-array-length z 36028797018963968
      (add-comm _ _ _ x-max) (ed-double-add _ _ ed-max-double) px))
  (lt-trans upper 72057594037927936 ed-value-limit
    (double-mono total 36028797018963968 upper 72057594037927936
      (lt-trans total z 36028797018963968 tz z-max2) twice ed-max2-double)
    ed-max4-small))

(def-fns _ $ (erased ed-dist-small : (erased (List (U8)) xs ys) (erased (Nat) d) (erased (Dist xs ys d) dist)
    (erased (Nat) nx ny) (erased (Length (U8) xs nx) lx) (erased (Length (U8) ys ny) ly)
    (erased (Lt nx max-array-length) px) (erased (Lt ny max-array-length) py) -> (erased (Lt d ed-value-limit) fits))
  (let ((erased total) (erased sum)) (add nx ny))
  (let ((erased upper) (erased twice)) (double total))
  (lt-le-trans d (Succ upper) ed-value-limit
    (le-lt d upper (ed-dist-bound xs ys d dist nx ny total upper lx ly sum twice))
    (LtS upper ed-value-limit (ed-length-sum-small nx ny total upper px py sum twice))))
