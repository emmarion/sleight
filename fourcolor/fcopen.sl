; four-color-open: FourColor of defs.sl from the steps whose proofs are computed: UnavE cfs (unav/qztproof.sl), AllRedC
; CRX css (red/proof-c.sl), BirkhoffChecks (red/bproof.sl) and CfCerts cfs (embed4proof.sl), for the css of red/chunks.sl.
; Load after evalid.sl, triad.sl, trivfive.sl, inductfc.sl and red/chunks.sl, in the chain PLAN.md gives.

(let ((many cfs) (erased cl)) (concat-c css))

(def-fns _ $ (erased four-color-open : (erased (UnavE cfs) u) (erased (AllRedC CRX css) ar) (erased (BirkhoffChecks) bks) (erased (CfCerts cfs) cc)
    -> (erased (FourColor) r))
  (four-color-from (embed-analysis CRX css cfs cl ar u (birk-geo-of bks) (not-embed cfs bks (full-red-of bks (triv-red-of triv-five)) cc (embed-valid bks) triad-five))))
