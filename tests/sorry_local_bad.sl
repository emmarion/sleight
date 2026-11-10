; `resolve` answers `RHypothetical` for a tainted local, so a macro that takes a constant refuses it as it
; would an untainted one.
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))
  (let-match erased (sorry (((Eq (Nat) n n) q))) (Refl _ _))
  (let ((many m)) (nat-add n 1))
  (unary m 3)
  m)
; error: tests/sorry_local_bad.sl:6:3: error: `unary` takes one or two constants of type `Nat` or `Char`
