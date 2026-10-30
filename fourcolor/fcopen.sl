; four-color-open: FourColor of defs.sl from the steps still open: UnavE cfs (unav/qztproof.sl), AllRedC CRX css
; (red/proof-c.sl) and BirkhoffChecks (red/bproof.sl), whose proofs are computed, and the hypotheses of notembed.sl
; (CfCerts, TriadFive) and fullred.sl (TrivRed), for the css of red/chunks.sl. Load after evalid.sl, inductfc.sl and
; red/chunks.sl, in the chain PLAN.md gives.

(let ((many cfs) (erased cl)) (concat-c css))

(def-fns _ $ (erased four-color-open : (erased (UnavE cfs) u) (erased (AllRedC CRX css) ar) (erased (BirkhoffChecks) bks) (erased (CfCerts cfs) cc)
    (erased (TrivRed) trd) (erased (TriadFive) tfv) -> (erased (FourColor) r))
  (four-color-from (embed-analysis CRX css cfs cl ar u (birk-geo-of bks) (not-embed cfs bks (full-red-of bks trd) cc (embed-valid bks) tfv))))
