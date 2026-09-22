; needs: list union
; error: not of newtype shape
; Two non-phantom union constructors with a many field each cannot be marked newtype.

(def-adts
  ((Both : ((Bool) tag) -> Type)
    union newtype
    (many BL : (many (Nat) n) -> (Both (BTrue)))
    (many BR : (many (Bool) b) -> (Both (BFalse)))))

(let ((many one)) (Succ (Zero)))
(coerce one (coercible-wrap (Shared) BL one))
