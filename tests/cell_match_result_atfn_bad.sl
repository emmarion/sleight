; error: `plain` has no `AtFn` proof in scope
(def-fns _ $ (many plain : (many (Nat) x) -> (many (Nat) r at x)) x)
(def-adts $ (C : -> Type) enum (many Ck : (many (Nat) n) -> (C)))
(def-fns _ $ (many forge : (unique (Cell Ck vacant-slot) u) -> (many (Slot) r))
  (let ((erased p) (many k)) (cell-match unique u (((AtFn (Fn (level-of plain) (many (Nat) x) -> (many (Nat) r at x)) plain) q) ((Slot) m)) (Ck n) (values (at-fn-of plain) n)))
  k)
