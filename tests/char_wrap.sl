; expect: (Succ (Succ (Zero)))
; char-to-nat destructures the newtype and the extern U8 with two let-matches; nat-to-char wraps out of
; range, as nat-to-u8 does (section 41), so every Nat names a Char and 258 comes back as 2.

(char-to-nat (nat-to-char (nat-add u8-modulus 2)))
