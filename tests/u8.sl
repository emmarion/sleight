; expect: 3
; U8 (section 41): a Nat below the modulus with an erased bound proof. The proof for a value built by hand
; comes by reflection, a comptime-match on the decided comparison.

(let ((many three)) (Succ (Succ (Succ (Zero)))))
(let ((many d)) (lt-dec three u8-modulus))
(comptime-match many d (Yes a b p))
(let ((many x)) (MkU8 three p))

(let-match many x (MkU8 xn xq))
(coerce x (coercible-sym (coercible-wrap (Shared) MkU8 xn xq)))
