; expect: (Cons _ 1 $ Cons _ 10 $ Cons _ 4 $ Cons _ 21 $ Cons _ 2 $ Cons _ 1 $ Cons _ 2 $ Cons _ 1 $ Nil _)
; U62 (section 41): its arithmetic takes Nats with erased proofs that neither operands nor results reach
; u62-modulus. The modulus is erased, so the bounds here are proved rather than computed: sixty-two is
; rebuilt and matched to the prelude's by add-fn and mul-fn, and a Pow2 exceeds its exponent.

(def-fns _ $ (erased double-le : (erased (Nat) a) (erased (Nat) b) (subterm erased (Double a b) d) -> (erased (Lt a (Succ b)) l))
  (match erased d _
    ((D0) (LtZ (Zero)))
    ((DS a1 b1 d1) (LtS a1 (Succ (Succ b1)) (lt-weaken a1 (Succ b1) (double-le a1 b1 d1))))))

(def-fns _ $ (erased pow2-gt : (erased (Nat) k) (erased (Nat) v) (subterm erased (Pow2 k v) p) -> (erased (Lt k v) l))
  (match erased p _
    ((P0) (LtZ (Zero)))
    ((PS k1 v1 w p1 d)
      (let ((erased ih)) (pow2-gt k1 v1 p1))
      (let ((erased vw))
        (match erased d (((Lt v1 w) x))
          (absurd (D0) ih)
          ((DS a b d1) (LtS a (Succ b) (double-le a b d1)))))
      (lt-le-trans (Succ k1) (Succ v1) w (LtS k1 v1 ih) (LtS v1 w vw)))))

(let ((many two)) (Succ (Succ (Zero))))
(let ((many three)) (Succ two))
(let ((many seven)) (Succ (Succ (Succ (Succ three)))))

(let ((many s60) (erased m60)) (mul (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (Succ (Succ eight))))
(let ((many s62) (erased a62)) (add s60 two))
(let ((erased e62))
  (match erased (mul-fn _ _ s60 sixty m60 sixty-mul) (((Eq (Nat) s62 sixty-two) e))
    ((Refl t r) (add-fn sixty two s62 sixty-two a62 sixty-two-add))))
(let ((erased big)) (pow2-gt sixty-two u62-modulus u62-modulus-pow2))

(def-fns _ $ (erased bounded : (erased (Nat) n) (erased (Lt n s62) p) -> (erased (Lt n u62-modulus) q))
  (match erased e62 _ ((Refl t r) (lt-trans n sixty-two u62-modulus p big))))

(let ((erased (Add seven three ten) sum)) (AddSucc _ _ _ $ AddSucc _ _ _ $ AddSucc _ _ _ $ AddSucc _ _ _ $ AddSucc _ _ _ $ AddSucc _ _ _ $ AddSucc _ _ _ $ AddZero three))
(let ((many prod) (erased mp)) (mul seven three))
(let ((many ds)) (lt-dec seven s62))
(comptime-match many ds (Yes a7 b7 p7))
(let ((many dt)) (lt-dec three s62))
(comptime-match many dt (Yes a3 b3 p3))
(let ((many dten)) (lt-dec ten s62))
(comptime-match many dten (Yes a10 b10 p10))
(let ((many dp)) (lt-dec prod s62))
(comptime-match many dp (Yes ap bp pp))

(def-lvl T)

(def-fns T $ (many main : -> (many (List (Nat)) r))
  (let ((many s)) (u62-add seven three ten sum (bounded ten p10)))
  (let ((many d) (erased df) (erased pd)) (u62-sub seven three (bounded seven p7) (LtS _ _ $ LtS _ _ $ LtS _ _ $ LtZ _)))
  (let ((many m)) (u62-mul seven three (bounded seven p7) (bounded three p3) prod mp (bounded prod pp)))
  (let ((many q) (many r) (erased k) (erased mm) (erased ad) (erased rl) (erased pq) (erased pr))
    (u62-divmod seven three (bounded seven p7) (bounded three p3) (LtZ _)))
  (let ((many q2) (erased k2) (erased r2) (erased mm2) (erased ad2) (erased rl2) (erased pq2))
    (u62-div seven three (bounded seven p7) (bounded three p3) (LtZ _)))
  (let ((many r3) (erased rl3) (erased md3) (erased pr3)) (u62-mod seven three (bounded seven p7) (bounded three p3) (LtZ _)))
  (let ((many lt)) (match many (u62-lt-dec three seven (bounded three p3) (bounded seven p7)) (((Nat) flag)) ((Yes a b p) 1) ((No a b p) 0)))
  (match many (u62-cmp three seven (bounded three p3) (bounded seven p7)) _
    ((CLt t rr x y p) (Cons _ lt $ Cons _ s $ Cons _ d $ Cons _ m $ Cons _ q $ Cons _ r $ Cons _ q2 $ Cons _ r3 $ Nil (Nat)))
    (absurd CEq)
    ((CGt t rr x y p) (Nil (Nat)))))

main
