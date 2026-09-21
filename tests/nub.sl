; needs: list vec lt_subterm
; expect: (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Nil _)
; Recursion on a computed vector, not a subterm: filter-ne returns the shorter vector with an erased bound on
; its length, and nub recurses on the erased length index, turned into the Subterm proof by lt-sub. The
; measure costs nothing at runtime.

(def-fns L $ erased lt-weaken : (subterm erased (Nat) b) (erased (Nat) a) (erased (Lt a b) p) -> (erased (Lt a (Succ b)) q)
  (match erased p _
    ((LtZ b1) (LtZ (Succ b1)))
    ((LtS a1 b1 p1) (LtS a1 (Succ b1) (lt-weaken (subterm (prove-subterm b1 b)) b1 a1 p1)))))

(def-lvl F)
(let (erased nf) (prove-predates nat-lvl F))
(let (erased lf) (prove-predates L F))
(def-fns F $ many filter-ne : (many (Nat) x) (erased (Nat) n) (subterm many (Vec (Nat) n) v) ->
    (erased (Nat) m) (many (Vec (Nat) m) w) (erased (Lt m (Succ n)) p)
  (match many v _
    ((VNil a) (values (Zero) (VNil (Nat)) (LtZ (Zero))))
    ((VCons a n1 y ys)
      (let (erased m1) (many w1) (erased p1) (filter-ne x n1 (subterm (prove-subterm ys v)) ys))
      (match many (lt-dec (predates nf) x y) (((Nat) m) ((Vec (Nat) m) w) ((Lt m (Succ n)) p))
        ((Yes q r lt) (values (Succ m1) (VCons (Nat) m1 y w1) (LtS m1 (Succ n1) p1)))
        ((No q r ge)
          (match many (lt-dec (predates nf) y x) (((Nat) m) ((Vec (Nat) m) w) ((Lt m (Succ n)) p))
            ((Yes q2 r2 lt2) (values (Succ m1) (VCons (Nat) m1 y w1) (LtS m1 (Succ n1) p1)))
            ((No q2 r2 ge2) (values m1 w1 (lt-weaken (predates lf) (Succ n1) m1 p1)))))))))

(def-lvl H)
(let (erased fh) (prove-predates F H))
(let (erased lh) (prove-predates L H))
(def-fns H $ many nub : (subterm erased (Nat) n) (many (Vec (Nat) n) v) -> (many (List (Nat)) out)
  (match many v _
    ((VNil a) (Nil (Nat)))
    ((VCons a n1 y ys)
      (let (erased m) (many w) (erased p) (filter-ne (predates fh) y n1 ys))
      (Cons (Nat) y (nub (subterm (lt-sub (predates lh) n m p)) m w)))))

(let (many one) (Succ (Zero)))
(let (many two) (Succ one))
(let (many three) (Succ two))
(let (many four) (Succ three))
(let (many five) (Succ four))
(let (many v) (VCons (Nat) four 1 (VCons (Nat) three 2 (VCons (Nat) two 1 (VCons (Nat) one 3 (VCons (Nat) (Zero) 2 (VNil (Nat))))))))
(nub five v)
