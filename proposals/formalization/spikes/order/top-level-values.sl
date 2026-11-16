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
(def-fns _ $ (many boom : (many (Nat) k) -> (many (Nat) r))
  (let ((erased _) (unique a) (erased _)) (array-make (Nat) 4611686018427387904 k))
  (let ((many len) (erased _) (unique _)) (array-length _ _ a))
  len)
(def-fns _ $ (many id-nat : (many (Nat) n) -> (many (Nat) m)) n)
(let ((many a) (many b)) (values (deep 100000) (id-nat (boom 7))))
(nat-add a b)
