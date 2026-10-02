; error: cannot infer `_?1` in `(V (Succ _?1))`
; An unresolved constructor return hole must be refused before its scope is discarded.
(def-adts $ (V : ((Nat) n) -> Type) enum
  (many VS : (erased (Nat) k) (erased (V k) v) -> (V (Succ _))))
