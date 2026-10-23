; externs: only
; expect: (Cons _ 101 $ Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 62 $ Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 1 $ Nil _)
; bit-length and bit-test past what the source models can compute: a Nat past 2^62, an index past what fits a
; host int, and the U62 versions at the top of their range, where the index may be 62.

(let ((many s60) (erased s60m)) (mul (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (Succ (Succ eight))))
(let-match erased (mul-fn _ _ _ _ s60m sixty-mul) (Refl _ _))
(let ((many s62) (erased s62a)) (add s60 (Succ (Succ (Zero)))))
(let-match erased (add-fn _ _ _ _ s62a sixty-two-add) (Refl _ _))
(let ((many u62m) (erased u62m-pow2) (erased _)) (pow2 s62))
(let-match erased (pow2-fn _ _ _ u62m-pow2 u62-modulus-pow2) (Refl _ _))
(let ((many top) (erased top-add)) (sub u62m (Succ (Zero)) (LtS _ _ u62-modulus-pos)))
(let ((many c-top)) (nat-cmp top u62m))
(comptime-match many c-top (CLt _ _ _ _ top-lt))
(let ((many c61)) (nat-cmp 61 (Succ s62)))
(comptime-match many c61 (CLt _ _ _ _ s61-lt))

(def-fns _ $ (many bit-nat : (many (Bit) x) -> (many (Nat) r))
  (match many x _ ((Bit0) 0) ((Bit1) 1)))

(let ((many big)) (nat-shl 1 100))
(let ((many lb) (erased _)) (bit-length big))
(let ((many t100) (erased _)) (bit-test big 100))
(let ((many t99) (erased _)) (bit-test big 99))
(let ((many tfar) (erased _)) (bit-test big 1180591620717411303424))
(let ((many lt) (erased _)) (u62-bit-length top top-lt))
(let ((many u61) (erased _)) (u62-bit-test top 61 top-lt s61-lt))
(let ((many u62) (erased _)) (u62-bit-test top s62 top-lt (lt-succ s62)))
(let ((many l0) (erased _)) (u62-bit-length (Zero) u62-modulus-pos))
(Cons _ lb $ Cons _ (bit-nat t100) $ Cons _ (bit-nat t99) $ Cons _ (bit-nat tfar) $ Cons _ lt $ Cons _ (bit-nat u61) $ Cons _ (bit-nat u62) $
  Cons _ l0 $ Cons _ (bit-nat $ nat-bit-test (nat-shl 1 99) 99) $ Nil _)
