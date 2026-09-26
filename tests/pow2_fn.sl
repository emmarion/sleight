; expect: 200
; pow2-fn: a Pow2 names one power per exponent, so a power computed afresh is the prelude's u8-modulus,
; and a bound checked against it at run time bounds a U8.
(def-fns _ $ (many to-u8 : (many (Nat) n) -> (many (Maybe (U8)) r))
  (let ((many m) (erased mp) (erased mpos)) (pow2 eight))
  (let-match many (lt-dec n m) (Yes _ _ lt) ((No _ _ _) (None _)))
  (match erased (pow2-fn _ _ _ mp u8-modulus-pow2) _
    ((Refl t x) (Some _ (MkU8 n lt)))))
(match many (to-u8 200) (((Nat) r))
  ((Some _ u) (let-match many u (MkU8 n p)) n)
  ((None _) 0))
