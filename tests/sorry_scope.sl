; A `let-match` on a tainted scrutinee taints the rest of the body it is in: `first` would reach a
; `Nil` with no branch for it if it ran. A branch of a match on a tainted scrutinee is tainted throughout.
(def-fns _ $ (many first : (many (List (Nat)) xs) -> (many (Nat) m))
  (let ((erased e)) (sorry (((Eq (List (Nat)) xs (Cons (Nat) 1 (Nil (Nat)))) q))))
  (let-match erased e (Refl _ _))
  (let-match many xs (Cons _ h _t))
  h)
(def-fns _ $ (many guarded : (many (Nat) n) -> (many (Nat) m) (many (Nat) k))
  (let ((many t)) (sorry (((Nat) x))))
  (let ((many r)) (match many t (((Nat) r)) ((Zero) n) ((Succ _p) n)))
  (values r n))
(let ((many _r) (many k)) (guarded 2))
(first (Cons (Nat) 1 (Nil (Nat))))
;! file "sorry/first-nil.sl"
(first (Nil (Nat)))
;! file "sorry/guarded.sl"
k
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_scope.sl:4:21: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
