; expect: 3
; Nat and Char convert without prelude help: an Lt makes the U8, MkChar wraps it, and two let-matches
; take it back apart.

(let ((many d)) (lt-dec 3 u8-modulus))
(comptime-match many d (Yes a b p))
(let ((many c)) (MkChar (MkU8 3 p)))
(let-match many c (MkChar u))
(let-match many u (MkU8 n q))
n
