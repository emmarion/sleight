; A `_` solved to a term that mentions a tainted entry taints its form: `(mkbox _)` would reach `absurd` code if
; it ran, and at run position it is not run, though nothing in it names `bad`.
(def-adts $ (Box : ((False) p) -> Type)
  enum
  (many MkBox : (erased (False) p) (many (Nat) n) -> (Box p)))
(def-fns _ $ (many absurd mkbox : (erased (False) p) -> (many (Box p) b))
  p)
(let ((erased bad)) (sorry (((False) q))))
(let ((many (Box bad) _v)) (mkbox _))
(def-fns _ $ (many boxed : (many (Nat) n) -> (many (Nat) m))
  (let ((many (Box bad) _w)) (mkbox _))
  (Succ n))
(boxed 6)
;! file "sorry/meta-used.sl"
(def-fns _ $ (many unboxed : (many (Nat) n) -> (many (Nat) m))
  (let ((many (Box bad) w)) (mkbox _))
  (let-match many w (MkBox _ k))
  (nat-add n k))
(unboxed 6)
; expect: 7
; expect: sorry
; warns: tests/sorry_meta.sl:8:21: warning: this unit uses `sorry` once, here; nothing that depends on it runs
