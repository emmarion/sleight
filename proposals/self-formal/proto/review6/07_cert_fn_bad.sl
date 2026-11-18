; Refused (round-6 review of 07): a function given a Certified value cannot call its step, whose level is packed.
; Run as spec.sl goal.sl det.sl impl.sl 07_cert_fn_bad.sl from proto/roundtrip/.
(def-fns _
  ((many init-top : (many (List $ Stmt) p) -> (many (CState p) s)) (start p))
  ((many step-top : (erased (List $ Stmt) p) (many (CState p) s) -> (many (Turn CState p) t)) (cstep p s))
  ((erased excl-top : (erased (List $ Stmt) p) (erased (Elab (Nil (Ent)) p) d) (erased (Fails (Nil (Ent)) p) f) ->
      (erased (False) no))
    (exclusive (Nil (Ent)) p d f)))
(def-fns _ $ (many first-turn : (many (Certified) c) (many (List $ Stmt) p) -> (many (Nat) r))
  (let-match many c (MkCertified S L init step excl))
  (let ((many s)) (init p))
  (match many (step p s) _ ((More _ _ _) 0) ((Fin _ _ _) 1)))
(first-turn (MkCertified CState _ init-top step-top excl-top) (Cons _ (Let $ Num 3) $ Nil _))
