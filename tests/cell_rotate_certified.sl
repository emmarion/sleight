; needs: cell_rotate
; expect: (Node (Leaf) 0 $ Node (Leaf) 1 $ Leaf)
; The same in-place rotation carrying the relation its result must satisfy. FlatOnto t acc out reads
; inorder(t) ++ acc = out; stating it in difference-list form is what lets the rotated tree's derivation
; be rebuilt from the original's without an associativity lemma. The relation's indices name t and l, the
; two cells the rotation overwrites, and every entry of the proof is declared erased (section 20).

(def-adts $ (Lst : -> Type)
  enum
  (many LNil : -> (Lst))
  (many LCons : (many (Nat) h) (many (Lst) t) -> (Lst)))

(def-adts
  ((FlatOnto : ((Tree) t) ((Lst) acc) ((Lst) out) -> Type)
    enum
    (many FLeaf : (erased (Lst) acc) -> (FlatOnto (Leaf) acc acc))
    (many FNode : (erased (Tree) l) (erased (Nat) v) (erased (Tree) r) (erased (Lst) acc)
                  (erased (Lst) m) (erased (Lst) out)
                  (erased (FlatOnto r acc m) pr) (erased (FlatOnto l (LCons v m) out) pl)
                  -> (FlatOnto (Node l v r) acc out))))

(def-fns _ $ (many rot-right-proved : (unique (Tree) t) (erased (Lst) acc) (erased (Lst) out)
    (erased (FlatOnto t acc out) p) -> (unique (Tree) r) (erased (FlatOnto r acc out) q))
  (match unique t _
    ((Leaf c) (values (Leaf) p))
    ((Node l y c outer)
      (match unique l _
        ((Leaf c2) (values (outer (Leaf) y c) p))
        ((Node a x b inner)
          (let-match erased p (FNode _ _ _ _ m1 _ pr pl))
          (let-match erased pl (FNode _ _ _ _ m2 _ pr2 pl2))
          (let ((unique nb)) (inner b y c))
          (values (outer a x nb)
                  (FNode a x (Node b y c) acc m2 out (FNode b y c acc m1 m2 pr pr2) pl2)))))))

(def-fns _ $ (many run-rot-proved : -> (many (Tree) r))
  (let ((unique t)) (Node (Node (Leaf) 0 (Leaf)) 1 (Leaf)))
  (let ((erased a1)) (LCons 1 (LNil)))
  (let ((erased o1)) (LCons 0 (LCons 1 (LNil))))
  (let ((erased fl))
    (FNode (Node (Leaf) 0 (Leaf)) 1 (Leaf) (LNil) (LNil) o1
      (FLeaf (LNil))
      (FNode (Leaf) 0 (Leaf) a1 a1 o1 (FLeaf a1) (FLeaf o1))))
  (let ((unique r) (erased q)) (rot-right-proved t (LNil) o1 fl))
  (share r))
run-rot-proved
