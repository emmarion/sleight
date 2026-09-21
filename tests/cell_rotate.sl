; expect: (Node (Leaf) 0 (Node (Leaf) 1 (Leaf)))
; A right rotation performed in place on branching data: both the outer node's cell and the left child's
; are handed back by their unique destructures and reinvoked with the rotated contents, so the rotation
; allocates nothing.

(def-adts $ Tree : -> Type
  enum
  (many Leaf : -> (Tree))
  (many Node : (unique (Tree) l) (many (Nat) v) (unique (Tree) r) -> (Tree)))

(def-fns _ $ many rot-right : (unique (Tree) t) -> (unique (Tree) r)
  (match unique t _
    ((Leaf c) (Leaf))
    ((Node l y c outer)
      (match unique l _
        ((Leaf c2) (outer (Leaf) y c))
        ((Node a x b inner)
          (let (unique nb) (inner b y c))
          (outer a x nb))))))

(def-fns _ $ many run-rot : -> (many (Tree) r)
  (let (unique t) (Node (Node (Leaf) 0 (Leaf)) 1 (Leaf)))
  (share (rot-right t)))
run-rot
