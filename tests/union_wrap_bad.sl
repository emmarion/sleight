; needs: list union
; error: not the wrapping constructor
; Two non-phantom union constructors with a many field each: no newtype, so no coercible-wrap.

(def-adts
  (Either : ((Bool) tag) -> Type
    union
    (many L : (many (Nat) n) -> (Either (True)))
    (many R : (many (Bool) b) -> (Either (False)))))

(let (many one) (Succ (Zero)))
(coerce one (coercible-wrap L one))
