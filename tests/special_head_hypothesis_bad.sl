; error: is not a statement
; A branch's hypothesis does not make a Settled head a special form: the head's minted type is read against run-position facts.
(def-fns _ $ (many make : -> (erased Type T) (many T v))
  (def-adts $ (Hidden : -> Type) enum (many Hid0 : -> (Hidden)))
  (values (Hidden) (Hid0)))

(let ((erased T) (many v)) (make))

(def-fns _ $ (many hyp : (erased (Eq Type T (Special)) p) -> (many (Nat) r))
  (match erased p (((Nat) r))
    ((Refl t x)
      (v ((many y)) (Zero))
      y)))

(Zero)
