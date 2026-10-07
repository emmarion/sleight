(def-fns _ $ (erased leak : (erased (TyCtor -> Type) T)
    (erased (ValCtor (erased Type A) (erased A x) -> (T)) C)
    (erased A y) -> (erased (Nat) r))
  (Zero))
; error: tests/valctor_binder_scope_bad.sl:3:13: error: unbound name `A`
