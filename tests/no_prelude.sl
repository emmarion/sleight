; prelude: none
; expect: (Node (Leaf) $ Node (Leaf) $ Leaf)
; A program run without lib/prelude.sl: only the built-in special forms are in scope, so it declares its own types.
(def-adts $ (Tree : -> Type) enum (many Leaf : -> (Tree)) (many Node : (many (Tree) l) (many (Tree) r) -> (Tree)))
(def-fns _ $ (many mirror : (subterm many (Tree) t) -> (many (Tree) r))
  (match many t _
    ((Leaf) (Leaf))
    ((Node l r) (Node (notail $ mirror r) (notail $ mirror l)))))
(mirror (Node (Node (Leaf) (Leaf)) (Leaf)))
