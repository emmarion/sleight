; needs: list
; expect: (Cons _ 0 $ Cons _ 1 $ Nil _)
; `_` inside an is clause and a type: solved from the neighbouring arguments, the nested Nil through the
; expectation the enclosing Cons hands down.

(def-adts $ (Two : ((Nat) a) ((Nat) b) -> Type)
  enum
  (many MkTwo : (erased (Nat) a) (erased (Nat) b) (many (Cons _ a (Cons _ b (Nil _))) is lst) -> (Two a b)))

(def-lvl L)
(def-fns L $ (many unpack : (erased (Nat) a) (erased (Nat) b) (many (Two a b) t) -> (many (List (Nat)) l))
  (match many t _
    ((MkTwo x y lst) lst)))

(let ((many z)) (Zero))
(let ((many o)) (Succ z))
(let ((many t)) (MkTwo _ _ (Cons _ z (Cons _ o (Nil _)))))
(unpack _ _ t)
