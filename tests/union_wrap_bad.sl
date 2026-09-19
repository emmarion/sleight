; needs: list union
; error: not of newtype shape
; Two non-phantom union constructors with a many field each cannot be marked newtype.

(def-adts
  (Either : ((Bool) tag) -> Type
    union newtype
    (many L : (many (Nat) n) -> (Either (True)))
    (many R : (many (Bool) b) -> (Either (False)))))

(let (many one) (Succ (Zero)))
(coerce one (coercible-wrap (Shared) L one))
