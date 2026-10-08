(def-adts $ (FB : ((Bool) b) -> Type) enum (many MkFB : (erased (Bool) b) -> (FB b)))
(def-adts $ (W : -> Type) enum
  (many MkW : (erased (TyCtor ((Nat) n) -> Type) G) (erased (Nat) j) (many (G j) v) -> (W)))
(def-fns _ $ (many mk : (erased (TyCtor ((Nat) n) -> Type) G) (erased (Nat) j) (many (G j) v) -> (many (W) w)) (MkW G j v))
(mk _ _ (MkFB (BTrue)))
; error: argument 3, `v`, of `mk`: type mismatch: expected `(TyCtor ((Nat) n) -> Type)`, got `(TyCtor ((Bool) b) -> Type)`: `_?1` would be `FB`
; error: tests/meta_type_call_bad.sl:5:5: note: `_?1` is the `_` written here
