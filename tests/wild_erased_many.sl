; needs: list
; expect: 1
; In an erased position a `_` may stand at a parameter declared many, the whole call being erased there;
; here the second parameter's is-entry solves it.

(def-lvl A)
(def-fns A $ many pick : (many (Nat) a) (many a is b) -> (many (Nat) r) b)
(let (erased p) (pick _ (Zero)))
(Succ (Zero))
