; needs: list
; expect: (Cons _ 0 $ Cons _ 1 $ Nil _)
; `_` at an is-entry takes the entry's value; a `_` inside the pinned field is solved through the is
; expectation, and the whole application against a value expectation.

(def-adts $ (Two : ((Nat) a) ((Nat) b) -> Type)
  enum
  (many MkTwo : (erased (Nat) a) (erased (Nat) b) (many (Cons (Nat) a (Cons (Nat) b (Nil (Nat)))) is lst) -> (Two a b)))

(def-lvl L)
(def-fns L $ (many unpack : (erased (Nat) a) (erased (Nat) b) (many (Two a b) t) -> (many (List (Nat)) l))
  (match many t _
    ((MkTwo _ _ lst) lst)))

(let ((many z)) (Zero))
(let ((many o)) (Succ z))
(let ((many t)) (MkTwo _ _ (Cons _ z (Cons _ o (Nil _)))))
(unpack _ _ t)
