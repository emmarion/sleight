; error: this `match` is missing a branch for the following unrefuted constructor:
; error: note: value constructor `TB`, which is declared here
; error: note: #\a in `(Tag (MkChar (MkU8 97 <**>)))` is a character literal, whose code is opaque to the checker by default; `unary`, `distinct` or `numeral-of` can expose more
; error: #\b is a character literal, whose code is opaque to the checker by default
; A character literal is transparent down to its code, a numeral (LITERALS.md), so the note names the
; character as written rather than its code, both the scrutinee's and the one TB's index forced it to.

(def-adts ((Tag : ((Char) c) -> Type)
  enum
  (many TA : -> (Tag #\a))
  (many TB : -> (Tag #\b))))
(def-lvl X)
(def-fns X $ (many only-a : (many (Tag #\a) t) -> (many (Nat) r))
  (match many t (((Nat) r))
    ((TA) (Zero))))
(only-a (TA))
