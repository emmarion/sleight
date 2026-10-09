; error: tests/let_binder_erased_pos_bad.sl:4:9: error: a `let` binder written `many` in an erased position; write `erased` here
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(def-fns _ $ (erased peek : (many (Box) b) -> (erased (Nat) r))
  (let ((many k)) (match many b (((Nat) v)) ((MkBox v) v)))
  k)
(Zero)
