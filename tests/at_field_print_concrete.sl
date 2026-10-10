; expect: (MkW $ MySucc $ MyZero)
; A printed value whose field is written `at` a variable of the enclosing scope: the block stores nothing,
; and the field prints from that variable's word.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(let ((many n)) (MySucc (MyZero)))
(def-adts $ (W : -> Type) enum (many MkW : (many (MyNat) m at n) -> (W)))
(MkW n)
