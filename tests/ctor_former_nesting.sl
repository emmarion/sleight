; expect: (MkBoxed 0)
; A ValCtor's return may name a type constructor bound by any enclosing former, one or two levels out: what
; ASSUMPTIONS 80 refuses is only a return headed by the constructor's own field. Here `one` takes a
; constructor into a type constructor from its own Fn telescope, and `two` takes a constructor whose field is
; itself a constructor into a type constructor bound beside it.
(def-adts $ Pair : (Type A) (Type B) -> Type
  enum
  (many MkPair : (erased Type A) (erased Type B) (many A a) (many B b) -> (Pair A B)))

(def-lvl X)
; one level out: T comes from the enclosing Fn telescope
(def-fns X $ many one : (erased (TyCtor -> Type) T) (many (ValCtor (many (Nat) n) -> (T)) C) (many (Nat) k) -> (many (T) x)
  (C k))

; two levels out: U is a binder of the outer ValCtor's own telescope, and the inner ValCtor returns (U)
(def-fns X $ many two : (erased (TyCtor -> Type) F)
    (many (ValCtor (erased (TyCtor -> Type) U) (erased (ValCtor -> (U)) C) -> (F)) Wrap)
    (erased (TyCtor -> Type) V) (erased (ValCtor -> (V)) D) -> (many (F) w)
  (Wrap V D))

(def-adts $ U1 : -> Type enum (many MkU1 : -> (U1)))
(def-adts $ Held : -> Type enum (many MkHeld : (erased (TyCtor -> Type) U) (erased (ValCtor -> (U)) C) -> (Held)))
(def-adts $ Boxed : -> Type enum (many MkBoxed : (many (Nat) n) -> (Boxed)))
(let (many h) (two Held MkHeld U1 MkU1))
(one Boxed MkBoxed (Zero))
