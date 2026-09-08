; error: MkBox has no Newtype in scope
; The same rule through newtype-of, where what a branch could have read itself out of the air is a Newtype for
; a constructor whose def-adts entry carries no newtype mark (section 38). (Box) is a tagged enum, so the
; coerce below would hand a (MkBox (Succ (Zero))) to a position of type (Nat).

(def-adts $ Box : -> Type
  enum
  (many MkBox : (many (Nat) n) -> (Box))
  (many Other : -> (Box)))

(let (erased w)
  (match erased (Zero) (((Newtype MkBox) w))
    (else (newtype-of MkBox))))

(let (many one) (Succ (Zero)))
(let (many n) (coerce (MkBox one) (coercible-sym (coercible-wrap MkBox one))))
n
