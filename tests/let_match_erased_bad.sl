; error: used in a non-erased position
; An erased scrutinee makes the bound fields erased, so nothing non-erased comes out of one.

(def-adts $ Box : -> Type enum (many MkBox : (many (Nat) v) -> (Box)))
(let (many b) (MkBox (Zero)))
(let (erased eb) (values b))
(let-match erased eb (MkBox v))
(def-lvl X)
(def-fns X $ many f : -> (many (Nat) n) v)
(Zero)
