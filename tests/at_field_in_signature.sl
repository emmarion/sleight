; expect: 3
; Applications of a constructor with a field written `at` inside a signature and a constructor's field, where
; the argument the `at` names is not a variable: `(slot-of v)`, and a newtype application, which is at its
; field.
(def-adts $ (W : ((Slot) s) -> Type) enum
  (many MkW : (erased (Slot) s) (erased (Nat) x at s) -> (W s)))
(def-adts $ (V : -> Type) enum
  (many MkV : (many (Copy (Nat)) m) (erased (Nat) x at m) -> (V)))
(def-fns _ $ (many f : (many (Nat) v) (erased (MkW (slot-of v) v) is w) (erased (MkV (MkCopy (Nat) v) v) is e) ->
    (many (Nat) r))
  v)
(let ((many a)) 3)
(def-adts $ (Q : -> Type) enum
  (many MkQ : (erased (Eq (V) (MkV (MkCopy (Nat) a) a) (MkV (MkCopy (Nat) a) a)) p) -> (Q)))
(let ((many q)) (MkQ (Refl _ _)))
(f a (MkW (slot-of a) a) (MkV (MkCopy (Nat) a) a))
