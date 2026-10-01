; error: `r`, declared `erased`, used in a non-erased position
; An erased binder is named as written, not by its canonical form.

(let ((erased Alias)) (Nat))

(def-lvl L)
(def-fns L $ (many same : (many (Nat) a) -> (many a is r))
  a)

(let ((many Alias x)) (Succ (Zero)))
(let ((erased r)) (same x))
(Succ r)
