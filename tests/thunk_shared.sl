; needs: list
; expect: 8
; A constant with much sharing: each pair holds the previous one twice, so its extraction must name shared
; parts rather than copy them, and the final function's code walks it.

(def-adts $ (Tree : -> Type)
  enum
  (many Leaf : -> (Tree))
  (many Node : (many (Tree) l) (many (Tree) r) -> (Tree)))

(def-lvl C)
(let ((erased nc)) (prove-predates nat-lvl C))
(def-fns C $ (many leaves : (subterm many (Tree) t) -> (many (Nat) n))
  (match many t _
    ((Leaf) (Succ (Zero)))
    ((Node l r) (nat-add (predates nc) (notail $ leaves (subterm _) l) (notail $ leaves (subterm _) r)))))

(let ((many t1)) (Node (Leaf) (Leaf)))
(let ((many t2)) (Node t1 t1))
(let ((many t3)) (Node t2 t2))

(def-lvl T)
(let ((erased ct)) (prove-predates C T))
(def-fns T $ (many main : -> (many (Nat) n))
  (leaves (predates ct) t3))

main
; warns: tests/thunk_shared.sl:16:57: warning: unnecessary `(subterm _)`; drop it
; warns: tests/thunk_shared.sl:16:89: warning: unnecessary `(subterm _)`; drop it
; warns: tests/thunk_shared.sl:16:26: warning: unnecessary `(predates _)`; drop it
; warns: tests/thunk_shared.sl:25:11: warning: unnecessary `(predates _)`; drop it
