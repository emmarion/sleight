; error: returns an application of a type constructor in scope
; A ValCtor's return names a type constructor in scope, not the constructor's own field: no def-adts could
; declare such a constructor, and nothing could find its type's Matchable.

(def-lvl X)
(def-fns X $ (many f : (erased (ValCtor (erased (TyCtor -> Type) T) -> (T)) C) (many (Nat) n) -> (many (Nat) r))
  (let ((erased p)) (coercible-ctor (Shared) C Nat Nat))
  n)
f
