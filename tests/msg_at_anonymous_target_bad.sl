(def-fns _ $ (many id-at : (many (Nat) y) (many (Nat) x) -> (many (Nat) r at x)) x)
(def-lvl K)
(def-fns _ $ (many mk : (many (Nat) x) -> (many (Fn K (many (Nat) y) -> (many (Nat) r at x)) g))
  (def-fns K $ (many h : (many (Nat) y) -> (many (Nat) r at x)) (id-at y x))
  h)
(let ((many g)) (mk (Succ 0)))
(g 3)
; error: tests/msg_at_anonymous_target_bad.sl:7:1: error: no caller word for `at` `_1`
; error: tests/msg_at_anonymous_target_bad.sl:7:1: note: `_1` is anonymous, minted by the elaborator rather than written in the source
; error: hint: give the argument it is at a name, with a `let`, before the call that takes it
