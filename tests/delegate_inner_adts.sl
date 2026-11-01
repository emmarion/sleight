; expect: 1
; A nested def-adts with non-phantom constructors does not block a delegate either: its constructors and
; Matchable are constants the body never mentions, so binding them only renames (DESIGN.md sections 19, 45).
(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-lvl M)
(let ((erased p)) (prove-predates L M))
(def-fns M $ (many g at inc : (many (Nat) n) -> (many (Nat) m))
  (def-adts $ (Tally : -> Type) enum (many Mark : (many (Nat) k) -> (Tally)) (many Blank : -> (Tally)))
  (delegate (inc (predates p) n)))
(let ((erased ig)) (coercible-of (delegate-of g)))
(g (Zero))
; warns: tests/delegate_inner_adts.sl:10:18: warning: unnecessary `(predates _)`; drop it
