(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za zb zp))
(let ((many code0)) (MkU8 0 zp))

(def-adts $ (WBox : -> Type)
  enum newtype
  (many MkWBox : (erased (World) w) (unique (Placed vacant-slot (World) w) p) -> (WBox)))

(def-fns _ $ (many say : (unique (World) w at vacant-slot) (many (String) s) -> (unique (WBox) b))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut s)))
  (MkWBox _ (place-at _ w1)))

(def-fns _ $ (many deep : (subterm many (Nat) n) -> (many (Nat) r))
  (let-match many n (Succ m) ((Zero) 0))
  (Succ (notail $ deep m)))

(def-lvl P)
(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique b) (many n)) (values (say w "A\n") (deep 100000)))
  (let-match unique b (MkWBox _ pw))
  (let ((unique w1)) (unplace-at _ _ _ pw))
  (let-match erased (placed-slot _ _ _ pw) (Refl _ _))
  (let ((unique w3) (many _)) (world-do _ w1 (WriteOut (str-append (nat-str n) "\n"))))
  (values w3 (Exit P code0)))
(Continue P start)
