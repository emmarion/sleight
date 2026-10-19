; error: `inc` and `dec` are not at one slot
(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns L $ (many dec : (many (Nat) n) -> (many (Nat) m)) n)
(let ((many s)) (fn-same inc dec))
; fn-same: yes
