; needs: ../std/macro macro_minted_sites_lib
; expect: (MkPair _ _ 3 _)
(with-nat (let ((many n))
  (def-fns _ $ (many f : (many (Nat) a at HERE) -> (many (Nat) r at a)) a)
  (f HERE)))
(with-slot (let ((many s)) (slot-self HERE) HERE))
(MkPair _ _ n s)
