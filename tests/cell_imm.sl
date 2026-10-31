; needs: ../std/immediate
; expect: (MkPair _ _ (MkTwo (MkU62 2 _) $ MkU62 1 _) $ MkTwo (MkU62 2 _) $ MkU62 2 _)
(def-adts $ (Two : -> Type)
  enum
  (many MkTwo : (many (U62) x) (many (U62) y) -> (Two)))

(def-fns _ $ (many swap-in : (unique (Two) t) (many (U62) z) -> (unique (Two) r at t))
  (let-match unique t (MkTwo x y u))
  (u (imm (ImmPlaced _ _ (imm-of _ (ImmU62) x) _ (place-at-many _ x)) (ImmPlaced _ _ (imm-of _ (ImmU62) y) _ (place-at-many _ y))) y
     (imm (ImmPlaced _ _ (imm-of _ (ImmU62) y) _ (place-at-many _ y)) (ImmPlaced _ _ (imm-of _ (ImmU62) z) _ (place-at-many _ z))) z))

(def-fns _ $ (many write-in : (unique (Two) t) (many (U62) z) -> (unique (Two) r at t))
  (let-match unique t (MkTwo x y u))
  (let ((unique u2))
    (cell-write unique u (MkTwo (imm (ImmPlaced _ _ (imm-of _ (ImmU62) x) _ (place-at-many _ x)) (ImmPlaced _ _ (imm-of _ (ImmU62) z) _ (place-at-many _ z))) (slot-of z) _)))
  (at unique (u2 z y)))

(def-fns _ $ (many fresh-in : (many (U62) z) -> (many (Two) r))
  (let ((unique u)) (cell-alloc MkTwo))
  (share (u (imm (ImmVacant) (ImmPlaced _ _ (imm-of _ (ImmU62) z) _ (place-at-many _ z))) z
            (imm (ImmVacant) (ImmPlaced _ _ (imm-of _ (ImmU62) z) _ (place-at-many _ z))) z)))

(def-fns _ $ (many char-u62 : (many (Char) c) -> (many (U62) u))
  (let-match erased c (MkChar b))
  (let-match erased b (MkU8 n p))
  (let ((erased q)) (lt-trans n u8-modulus u62-modulus p u8-below-u62))
  (coerce c (coercible-trans
              (coercible-trans (coercible-sym (coercible-wrap (Shared) MkChar b)) (coercible-sym (coercible-wrap (Shared) MkU8 n p)))
              (coercible-wrap (Shared) MkU62 n q))))

(def-fns _ $ (many main : -> (many (Pair (Two) (Two)) r))
  (let ((many one)) (char-u62 #\x01))
  (let ((many two)) (char-u62 #\x02))
  (let ((unique t)) (MkTwo one (MkU62 (Zero) u62-modulus-pos)))
  (let ((unique t2)) (swap-in t one))
  (let ((unique t3)) (write-in t2 two))
  (MkPair _ _ (share t3) (fresh-in two)))

main
