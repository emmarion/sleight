; needs: list vec
; expect: (VCons _ _ 1 $ VNil _)
; A dependent motive: each branch's result is checked against (Vec B n) under that branch's facts.

(def-lvl M)
(def-fns M $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(def-lvl V)
(let ((erased p)) (prove-predates M V))

(def-fns V $ (many vmap : (erased (Nat) n) (subterm many (Vec (Nat) n) v) -> (many (Vec (Nat) n) r))
  (match many v (((Vec (Nat) n) r))
    ((VNil a) (VNil (Nat)))
    ((VCons a m x xs)
      (let ((erased q)) (prove-subterm xs v))
      (VCons (Nat) m (inc (predates p) x) (vmap m (subterm q) xs)))))

(vmap (Succ (Zero)) (VCons (Nat) (Zero) (Zero) (VNil (Nat))))
