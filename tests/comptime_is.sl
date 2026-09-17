; needs: list
; expect: 0
; comptime-match facts persist at the top level: a later let can pin a binder by is.

(def-lvl W)
(def-fns W $ many id : (many (Nat) n) -> (many (Nat) m) n)
(let (many two) (id (Succ (Succ (Zero)))))
(comptime-match two (Succ one))
(comptime-match one (Succ zero))
(let (many (Succ (Succ zero)) is two2) two)
(let (many zero is z) zero)
z
