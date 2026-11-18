; Accepted (round-7 review of 07): a function given a Certified value, made before its level was minted, and a
; Predates about that value calls its init and step through predates-subterm. Run as spec.sl goal.sl det.sl
; impl.sl 07_cert_predates.sl from proto/roundtrip/.
(def-fns _
  ((many init-top : (many (List $ Stmt) p) -> (many (CState p) s)) (start p))
  ((many step-top : (erased (List $ Stmt) p) (many (CState p) s) -> (many (Turn CState p) t)) (cstep p s))
  ((erased excl-top : (erased (List $ Stmt) p) (erased (Elab (Nil (Ent)) p) d) (erased (Fails (Nil (Ent)) p) f) ->
      (erased (False) no))
    (exclusive (Nil (Ent)) p d f)))
(let ((many c0)) (MkCertified CState _ init-top step-top excl-top))
(def-lvl F)
(def-fns F $ (many first-turn : (many (Certified) c) (erased (Predates (Certified) c F) pc) (many (List $ Stmt) p) -> (many (Nat) r))
  (let-match many c (MkCertified S L init step excl))
  (let ((erased ps)) (prove-subterm L c))
  (let ((erased pl)) (predates-subterm pc ps))
  (let ((many s)) (init (predates pl) p))
  (match many (step (predates pl) p s) _ ((More _ _ _) 0) ((Fin _ _ _) 1)))
(let ((erased pc0)) (prove-predates c0 F))
(first-turn c0 pc0 (Cons _ (Let $ Num 3) $ Nil _))
