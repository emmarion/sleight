(def-adts $ (T : -> Type)
  enum
  (many MkT : (erased (False) g) -> (T)))
(def-adts $ (U : -> Type)
  enum
  (many MkU : (erased (ValCtor (erased (False) f) -> (T)) c) (erased (Eq (False) f f) e) -> (U)))
; error: tests/valctor_binder_field_bad.sl:6:82: error: unbound name `f`
