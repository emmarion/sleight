; needs: list
; expect: (Succ (Zero))
; In an erased call a `_` may stand at a many parameter, and a pure argument's `_` is solved by the proof
; argument after it in the same call, whose type mentions the value.
(def-adts $ Wrapped : ((Nat) n) -> Type
  enum
  (many MkWrapped : (erased (Nat) n) -> (Wrapped n)))
(def-lvl L)
(def-fns L $ erased unwrap : (many (Nat) n) (erased (Wrapped n) w) -> (erased (Nat) m) n)
(let (many z) (Zero))
(let (erased p) (unwrap (Succ _) (MkWrapped (Succ z))))
(Succ z)
