; expect: 0
; A later parameter's type names the slot of an earlier one, and the argument for that one is a binder
; whose `is` rule is a constructor application: the slot named is the binder's (section 35), as for a
; literal or a parameter.
(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (many (Nat) b) -> (P)))
(def-fns _ $ (many k : (many (Nat) x) (unique (Cell MkP (slot-of x) vacant-slot) u) -> (many (Nat) r))
  (let-match many (share (u (at) x 0)) (MkP _ b))
  b)
(let ((many p)) (Succ (Zero)))
(let ((unique u)) (cell-alloc (MkP (slot-of p) _)))
(k p u)
