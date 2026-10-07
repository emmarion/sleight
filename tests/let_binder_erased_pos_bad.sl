; error: tests/let_binder_erased_pos_bad.sl:4:9: error: a `let` binder in an erased position is written `erased`
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(def-fns _ $ (erased peek : (many (Box) b) -> (erased (Nat) r))
  (let ((many k)) (match many b (((Nat) v)) ((MkBox v) v)))
  k)
(Zero)
