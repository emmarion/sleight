(def-adts $ (T : -> Type)
  enum
  (many MkT : (erased (False) g) -> (T)))
(def-fns _ $ (erased bad : (erased (ValCtor (erased (False) f) -> (T)) c) (erased f is p) ->
    (erased (False) r))
  p)
(let ((erased (False) h)) (bad MkT _))
(def-fns _ $ (many absurd boom : -> (many (Nat) n)) h)
boom
; error: tests/valctor_binder_false_bad.sl:4:83: error: unbound name `f`
