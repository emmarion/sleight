; error: does not satisfy `at`
; As tests/at_field_in_signature.sl, the newtype application at a variable other than the one written `at` it.
(def-adts $ (V : -> Type) enum
  (many MkV : (many (Copy (Nat)) m) (erased (Nat) x at m) -> (V)))
(def-fns _ $ (many f : (many (Nat) v) (many (Nat) w) (erased (MkV (MkCopy (Nat) v) w) is e) -> )
  (values))
