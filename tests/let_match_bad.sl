; error: needs an ordinary match
; let-match wants a type whose Matchable lists one constructor; Nat lists two.

(let (many x) 5)
(let-match many x (Succ p))
(Zero)
