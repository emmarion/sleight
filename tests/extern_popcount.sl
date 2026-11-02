; expect: (Cons _ 3 $ Cons _ 0 $ Cons _ 1 $ Cons _ 3 $ Cons _ 4 $ Cons _ 0 $ Cons _ 2 $ Cons _ 5 $ Cons _ 3 $ Cons _ 5 $ Nil _)
; popcount through PopCount and trailing-zeros through TrailingZeros, which needs a positive argument; their
; U62 versions under bounds, and the functionality lemmas. Each runs once at elaboration and once inside a
; function.

(unary 0)
(let ((erased p40)) (lt-trans _ _ _ (prove-literal-lt 40 u8-modulus) u8-below-u62))
(let ((erased p96)) (lt-trans _ _ _ (prove-literal-lt 96 u8-modulus) u8-below-u62))

(let ((many c11) (erased pc11)) (popcount 11))
(let ((erased (Eq (Nat) c11 c11) _)) (popcount-fn _ _ _ pc11 pc11))
(let ((many t40) (erased pt40)) (trailing-zeros 40 (prove-literal-lt 0 40)))
(let ((erased (Eq (Nat) t40 t40) _)) (trailing-zeros-fn _ _ _ pt40 pt40))

(def-lvl A)
(def-fns A $ (many bits : -> (many (List (Nat)) out))
  (let ((many c0) (erased _)) (popcount 0))
  (let ((many c1) (erased _)) (popcount 1))
  (let ((many c15) (erased _)) (popcount 15))
  (let ((many u40) (erased _)) (u62-popcount 40 p40))
  (let ((many t1) (erased _)) (trailing-zeros 1 (prove-literal-lt 0 1)))
  (let ((many t96) (erased _)) (trailing-zeros 96 (prove-literal-lt 0 96)))
  (let ((many v96) (erased _)) (u62-trailing-zeros 96 p96 (prove-literal-lt 0 96)))
  (Cons _ c11 $ Cons _ c0 $ Cons _ c1 $ Cons _ t40 $ Cons _ c15 $ Cons _ t1 $ Cons _ u40 $ Cons _ t96 $ Cons _ t40 $ Cons _ v96 $ Nil _))

bits
