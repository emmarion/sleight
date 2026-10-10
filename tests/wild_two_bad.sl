; error: cannot infer `__?1` and `__?2` in `(Pair __?1 __?2)`
; error: `__?1` is the `_` written here
; error: `__?2` is the `_` written here
; Two metas in one message are numbered in the order they first appear, and each gets a note naming
; where its `_` is written.

(def-lvl L)
(def-fns L $ (many f : (many (Pair _ _) p) -> (many (Nat) n))
  (Zero))
(Zero)
