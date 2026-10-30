; FourColor of defs.sl from the steps still open, as one goal: UnavE (unav/qztgoal.sl), AllRedC CRX (red/goal-c.sl) and
; BirkhoffChecks (red/bgoal.sl), whose computed proofs run in units of their own, and the hypotheses of embed5.sl
; (FullRed, PatchOpen) and notembed.sl (GcFun, EmbedValid, ContractLater). Load after notembed.sl and inductfc.sl, in the
; chain PLAN.md gives.

(let ((many css)) (config-chunks))
(let ((many cfs) (erased cl)) (concat-c css))

(def-adts $ (FourColorOpen : -> Type)
  enum
  (many MkFourColorOpen : (erased (Level) F)
      (erased (Fn F (erased (UnavE cfs) u) (erased (AllRedC CRX css) ar) (erased (BirkhoffChecks) bks) (erased (FullRed) frd) (erased (PatchOpen) po)
          (erased (GcFun cfs) gf) (erased (EmbedValid) ev) (erased (ContractLater) ctl) -> (erased (FourColor) r)) fc)
      -> (FourColorOpen)))

(def-fns _ $ (erased four-color-open : (erased (UnavE cfs) u) (erased (AllRedC CRX css) ar) (erased (BirkhoffChecks) bks) (erased (FullRed) frd)
    (erased (PatchOpen) po) (erased (GcFun cfs) gf) (erased (EmbedValid) ev) (erased (ContractLater) ctl) -> (erased (FourColor) r))
  (four-color-from (embed-analysis CRX css cfs cl ar u (birk-geo-of bks) (not-embed cfs bks frd po gf ev ctl))))

(goal erased (FourColorOpen))
(qed (MkFourColorOpen (level-of four-color-open) four-color-open))
