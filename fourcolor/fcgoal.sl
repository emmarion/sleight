; The goal FourColorOpen: four-color-open of fcopen.sl, packaged with its level. Load after fcopen.sl.

(def-adts $ (FourColorOpen : -> Type)
  enum
  (many MkFourColorOpen : (erased (Level) F)
      (erased (Fn F (erased (UnavE cfs) u) (erased (AllRedC CRX css) ar) (erased (BirkhoffChecks) bks) (erased (CfCerts cfs) cc)
          (erased (TrivFive) t5) -> (erased (FourColor) r)) fc)
      -> (FourColorOpen)))

(goal erased (FourColorOpen))
(qed (MkFourColorOpen (level-of four-color-open) four-color-open))
