; The goal FourColorRest: FourColor of defs.sl from the hypotheses of notembed.sl (CfCerts, TriadFive) and fullred.sl
; (TrivRed) alone, by four-color-open of fcopen.sl on the computed unav-proof, all-red-proof and birkhoff-proof. Load after
; unav/qztproof.sl, in the chain PLAN.md gives.

(def-adts $ (FourColorRest : -> Type)
  enum
  (many MkFourColorRest : (erased (Level) F)
      (erased (Fn F (erased (CfCerts cfs) cc) (erased (TrivRed) trd) (erased (TriadFive) tfv) -> (erased (FourColor) r)) fc)
      -> (FourColorRest)))

(def-fns _ $ (erased four-color-rest : (erased (CfCerts cfs) cc) (erased (TrivRed) trd) (erased (TriadFive) tfv) -> (erased (FourColor) r))
  (four-color-open unav-proof all-red-proof birkhoff-proof cc trd tfv))

(goal erased (FourColorRest))
(qed (MkFourColorRest (level-of four-color-rest) four-color-rest))
