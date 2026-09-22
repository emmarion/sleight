; expect: (MkPair _ _ (PLeft) $ PRight)
; Constructor return holes may be solved by later arguments or their expected types.
(def-adts $ (P : (Type A) ((List A) xs) -> Type) enum
  (many PLeft : -> (P _ (Nil (Nat))))
  (many PRight : -> (P (Nat) (Nil _))))
(let ((erased LeftCtor)) (ValCtor -> (P _ (Nil (Nat)))))
(let ((erased RightCtor)) (ValCtor -> (P (Nat) (Nil _))))
(let ((many LeftCtor left)) PLeft)
(let ((many RightCtor right)) PRight)
(MkPair _ _ (left) (right))
