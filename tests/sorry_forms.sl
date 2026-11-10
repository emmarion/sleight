; `sorry` at each multiplicity, with a written telescope, with an `is` entry, and with `_` for the telescope its
; position expects. Checking goes on past it: the `is` entry's rule is in force, and what does not depend on it runs.
(let ((erased _p)) (sorry (((Lt 1 2) q))))
(let ((unique _u)) (sorry (((List (Nat)) x))))
(let ((many k) (many j)) (sorry ((3 is x) ((Nat) y))))
(let ((erased 3 is _k3)) k)
(def-fns _ $ (many guess : (many (Nat) _n) -> (many (Nat) m) (erased (Lt m 2) p))
  (sorry _))
(MkPair (Nat) (Nat) 1 2)
;! file "sorry/forms.sl"
(MkPair (Nat) (Nat) 1 j)
; expect: (MkPair _ _ 1 2)
; expect: sorry
; warns: tests/sorry_forms.sl:3:20: warning: this unit uses `sorry` 4 times, first here; nothing that depends on it runs
