; expect: (Cons _ 0 $ Nil _)
; A type computed by a call is usable as what it computed when the return entry says so: list-of returns
; its result as an is entry, so LN canonicalizes to (List (Nat)) and a let annotated LN accepts a list of Nat.

(def-lvl T)
(def-fns T $ erased list-of : (erased Type A) -> (erased (List A) is B)
  (List A))

(let (erased LN) (list-of (Nat)))
(let (many LN xs) (Cons (Nat) (Zero) (Nil (Nat))))
xs
