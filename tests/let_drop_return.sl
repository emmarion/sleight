; needs: list
; expect: 1
; A let binding a many return erased still receives the later returns in order, at the top level and in a body.

(def-lvl L)
(def-fns L $ (many two : (many (Nat) n) -> (many (Nat) a) (many (Nat) b)) (values n (Succ n)))
(def-lvl M)
(let ((erased p)) (prove-predates L M))
(def-fns M $ (many second : (many (Nat) n) -> (many (Nat) r))
  (let ((erased _) (many b)) (two (predates p) n))
  b)

(let ((erased a) (many b)) (two (Zero)))
(comptime-match many b (Succ z))
(second z)
; warns: tests/let_drop_return.sl:10:35: warning: unnecessary `(predates _)`; drop it
