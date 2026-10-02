; error: cannot infer the `_` in `(Pair _?1 _?2)`
; error: `_?1` is the `_` written here
; error: `_?2` is the `_` written here
; Two metas in one message are numbered in the order they first appear, and each gets a note naming
; where its `_` is written.

(def-lvl L)
(def-fns L $ (many f : (many (Pair _ _) p) -> (many (Nat) n))
  (Zero))
(Zero)
