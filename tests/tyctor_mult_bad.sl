(def-adts ((Foo : (Type a) (erased (Type) x) -> Type) enum))
; error: tests/tyctor_mult_bad.sl:1:28: error: a type constructor's parameters take no multiplicity; drop `erased`
