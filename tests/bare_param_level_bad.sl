; needs: list
; error: was not in scope when level
; A bare call to a function whose level is a parameter: the levels differ, so a Predates proof is
; inferred, and prove-predates refuses a level bound after the current one was minted; DESIGN.md
; section 57's factory supplies the proof by hand.

(def-lvl L)
(def-fns L $ (many apply-all : (erased (Level) M) (many (Fn M (many (Nat) x) -> (many (Nat) y)) f) (many (Nat) x) -> (many (Nat) y))
  (f x))
