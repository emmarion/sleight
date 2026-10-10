(def-adts $ (FB : ((Bool) b) -> Type) enum (many MkFB : (erased (Bool) b) -> (FB b)))
(def-adts $ (W : -> Type) enum
  (many MkW : (erased (TyCtor ((Nat) n) -> Type) G) (erased (Nat) j) (many (G j) v) -> (W)))
(let ((many w)) (MkW _ _ (MkFB (BTrue))))
(def-fns _ $ (many run : -> (many (False) n)) (match many w (((False) r))))
run
; error: argument 3, `v`, of `MkW`: type mismatch: expected `(TyCtor ((Nat) n) -> Type)`, got `(TyCtor ((Bool) b) -> Type)`: `_?1` would be `FB`
; error: tests/meta_type_ctor_bad.sl:4:22: note: `_?1` is the `_` written here
