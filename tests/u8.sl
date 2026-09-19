; expect: 3
; U8 (section 41): a Nat below the modulus with an erased bound proof. The proof for a value built by hand
; comes by reflection, a comptime-match on the decided comparison; addition wraps at 256.

(let (many three) (Succ (Succ (Succ (Zero)))))
(let (many d) (lt-dec three u8-modulus))
(comptime-match many d (Yes a b p))
(let (many x) (MkU8 three p))

(let (many two) (Succ (Succ (Zero))))
(let (many four) (nat-add two two))
(let (many sixteen) (nat-add (nat-add four four) (nat-add four four)))
(let (many half) (nat-add (nat-add (nat-add sixteen sixteen) (nat-add sixteen sixteen))
                          (nat-add (nat-add sixteen sixteen) (nat-add sixteen sixteen))))
(let (many dh) (lt-dec half u8-modulus))
(comptime-match many dh (Yes ah bh ph))
(let (many h) (MkU8 half ph))
(let (many wrapped) (u8-add h (u8-add h x)))
(let-match many wrapped (MkU8 wn wq))
(coerce wrapped (coercible-sym (coercible-wrap MkU8 wn wq)))
