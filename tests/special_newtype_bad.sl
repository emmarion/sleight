; error: is not applicable
; A Const holding a Special variant heads a form only when its type is (Special) too: coercing let into a newtype
; around Special gives a value whose stored value is (%let) but whose type is (W), and it is not a special form.

(def-adts $ W : -> Type
  enum newtype
  (many MkW : (many (Special) s) -> (W)))

(let (many w) (coerce let (coercible-wrap (Shared) MkW let)))
(w (many x) (Succ (Zero)))
