; The goal FourColorRest: FourColor of defs.sl from the hypotheses of fullred.sl (TrivRed) and notembed.sl (TriadFive)
; alone, by four-color-open of fcopen.sl on the computed unav-proof, all-red-proof, birkhoff-proof and cfcerts-proof. Load
; after unav/qztproof.sl, in the chain PLAN.md gives.

(def-adts $ (FourColorRest : -> Type)
  enum
  (many MkFourColorRest : (erased (Level) F)
      (erased (Fn F (erased (TrivRed) trd) (erased (TriadFive) tfv) -> (erased (FourColor) r)) fc)
      -> (FourColorRest)))

(def-fns _ $ (erased four-color-rest : (erased (TrivRed) trd) (erased (TriadFive) tfv) -> (erased (FourColor) r))
  (four-color-open unav-proof all-red-proof birkhoff-proof cfcerts-proof trd tfv))

(goal erased (FourColorRest))
(qed (MkFourColorRest (level-of four-color-rest) four-color-rest))
