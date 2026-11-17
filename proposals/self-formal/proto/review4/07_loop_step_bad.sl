; Refused (fourth review of 07): a step-top that calls itself. Run as --goal proved spec.sl goal.sl det.sl
; impl.sl 07_loop_step_bad.sl from proto/roundtrip/.
(def-fns _
  ((many init-top : (many (List $ Stmt) p) -> (many (CState p) s)) (start p))
  ((many step-top : (erased (List $ Stmt) p) (many (CState p) s) -> (many (Turn CState p) t)) (step-top p s))
  ((erased excl-top : (erased (List $ Stmt) p) (erased (Elab (Nil (Ent)) p) d) (erased (Fails (Nil (Ent)) p) f) ->
      (erased (False) no))
    (exclusive (Nil (Ent)) p d f)))
(qed (MkCertified CState _ init-top step-top excl-top))
