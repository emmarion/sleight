; needs: list vec
; expect: (VCons _ _ 0 $ VCons _ _ 1 $ VCons _ _ 2 $ VNil _)
; Vector append with the sum witnessed by an erased Plus proof: each erased match on the
; proof has one real branch, the other refuted through the indices.

(def-adts
  ((Plus : ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many PZ : (erased (Nat) b) -> (Plus (Zero) b b))
    (many PS : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (many (Plus a b c) p)
       -> (Plus (Succ a) b (Succ c)))))

(def-lvl V)

(def-fns V $ (many vappend : (erased Type A) (erased (Nat) n) (erased (Nat) m) (erased (Nat) k)
    (erased (Plus n m k) p) (subterm many (Vec A n) xs) (many (Vec A m) ys) -> (many (Vec A k) zs))
  (match many xs (((Vec A k) zs))
    ((VNil a)
      (match erased p (((Vec A k) zs))
        ((PZ b) ys)
        (absurd PS)))
    ((VCons a n2 x xs2)
      (match erased p (((Vec A k) zs))
        (absurd PZ)
        ((PS a2 b c q)
          (let ((erased sp)) (prove-subterm xs2 xs))
          (VCons A c x (vappend A n2 m c q (subterm sp) xs2 ys)))))))

(let ((many one)) (Succ (Zero)))
(let ((many two)) (Succ one))
(let ((many xs)) (VCons (Nat) one (Zero) (VCons (Nat) (Zero) one (VNil (Nat)))))
(let ((many ys)) (VCons (Nat) (Zero) two (VNil (Nat))))
(vappend (Nat) two one (Succ two) (PS one one two (PS (Zero) one one (PZ one))) xs ys)
