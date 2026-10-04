; externs: only
; expect: (Cons _ 1267650600228229401496703205376 $ Cons _ 4 $ Cons _ 0 $ Cons _ 0 $ Cons _ 3 $ Cons _ 0 $ Cons _ 1267650600228229401496703205376 $ Cons _ 1901475900342344102245054808064 $ Cons _ 0 $ Cons _ 4611686018427387903 $ Nil _)
; Shifts and bitwise operations past what the source models can compute: a Nat shl past 2^62, a Nat shr by more
; than fits a host int, the U62 shifts at their largest count, 62, Nat bitwise past 2^62 and U62's at its top.

(let ((many s60) (erased s60m)) (mul (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) (Succ (Succ eight))))
(let-match erased (mul-fn _ _ _ _ s60m sixty-mul) (Refl _ _))
(let ((many s62) (erased s62a)) (add s60 (Succ (Succ (Zero)))))
(let-match erased (add-fn _ _ _ _ s62a sixty-two-add) (Refl _ _))
(let ((many u62m) (erased u62m-pow2) (erased _)) (pow2 s62))
(let-match erased (pow2-fn _ _ _ u62m-pow2 u62-modulus-pow2) (Refl _ _))

(let ((many top) (erased top-add)) (sub u62m (Succ (Zero)) (LtS _ _ u62-modulus-pos)))
(let ((many c-top)) (nat-cmp top u62m))
(comptime-match many c-top (CLt _ _ _ _ top-lt))
(let ((many c60)) (nat-cmp s60 (Succ s62)))
(comptime-match many c60 (CLt _ _ _ _ s60-lt))

(let ((many big)) (nat-shl 1 100))
(let ((many z)) (u62-shl (Zero) s62 (lt-succ s62) u62m u62-modulus-pow2 (Zero) (MulZero u62m) u62-modulus-pos))
(let ((many t62) (erased v) (erased pv) (erased m) (erased r) (erased mm) (erased ad) (erased rl) (erased pq))
  (u62-shr top s62 top-lt (lt-succ s62)))
(let ((many t60) (erased v6) (erased pv6) (erased m6) (erased r6) (erased mm6) (erased ad6) (erased rl6) (erased pq6))
  (u62-shr top s60 top-lt s60-lt))
(let ((many ba) (erased pba)) (nat-and big (nat-shl 3 99)))
(let ((many bo) (erased pbo)) (nat-or big (nat-shl 1 99)))
(let ((many bx) (erased pbx)) (nat-xor big big))
(let ((many tx) (erased ptx)) (u62-xor top (Zero) top-lt u62-modulus-pos))
(Cons _ big $ Cons _ (nat-shr big 98) $ Cons _ (nat-shr 5 1180591620717411303424) $ Cons _ z $ Cons _ t60 $ Cons _ t62 $
  Cons _ ba $ Cons _ bo $ Cons _ bx $ Cons _ tx $ Nil _)
