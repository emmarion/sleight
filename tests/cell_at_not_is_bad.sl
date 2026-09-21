; needs: cell_rotate cell_rotate_certified
; error: type mismatch
; The converse of at_is_independent_bad.sl, and what lets a proof outlive the memory it describes: the
; rotation's result is at t, the same word, but it is not is t, so the relation proved of t before the
; rotation is refused where one about r is wanted. Location and value are compared separately (UNIQUE.md
; U8), which is why an erased mention of an overwritten binder states the old contents and nothing else.

(def-fns _ $ many stale : -> (many (Tree) out)
  (let (unique t) (Node (Node (Leaf) 0 (Leaf)) 1 (Leaf)))
  (let (erased a1) (LCons 1 (LNil)))
  (let (erased o1) (LCons 0 (LCons 1 (LNil))))
  (let (erased fl)
    (FNode (Node (Leaf) 0 (Leaf)) 1 (Leaf) (LNil) (LNil) o1
      (FLeaf (LNil))
      (FNode (Leaf) 0 (Leaf) a1 a1 o1 (FLeaf a1) (FLeaf o1))))
  (let (unique r) (erased q) (rot-right-proved t (LNil) o1 fl))
  (let (erased (FlatOnto r (LNil) o1) reused) fl)
  (share r))
stale
