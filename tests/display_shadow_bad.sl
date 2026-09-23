; error: error: type mismatch: expected `(Eq (Nat) <**> <**>)`, got `(Eq (Nat) n n)`
; A name is shown only where it still denotes the atom: here the field n shadows the parameter n, so the
; parameter is shown by its id and the message cannot read as n differing from itself.

(def-fns _ $ (erased f : (many (Nat) n) (many (Nat) m) -> (erased (Eq (Nat) n n) r))
  (match erased m (((Eq (Nat) n n) r))
    ((Zero) (Refl (Nat) n))
    ((Succ n) (Refl (Nat) n))))
(Zero)
; warns: tests/display_shadow_bad.sl:8:12: warning: declaration of `n` shadows a previous binder
; warns: tests/display_shadow_bad.sl:5:26: note: shadowed binder is here
