; expect: 1
; As slot_of_param_type_ruled.sl, with the slot named by the `at` of a parameter's function type, and the
; call inside a body where the binder is `Dyn`.
(def-lvl L)
(def-fns _ $ (many call2 : (many (Nat) x) (many (Fn L (many (Nat) w at x) -> (many (Nat) r at x)) f) -> (many (Nat) r at x))
  (f x))
(def-fns _ $ (many go : (many (Nat) n) -> (many (Nat) r))
  (let ((many p)) (Succ n))
  (def-fns L $ (many g : (many (Nat) w at p) -> (many (Nat) r at p)) w)
  (call2 p g))
(go 0)
