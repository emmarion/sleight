; four-color-open: FourColor of defs.sl from the steps whose proofs are computed: UnavE cfs (unav/qztproof.sl), AllRedC
; CRX css (red/proof-c.sl), BirkhoffChecks (red/bproof.sl) and CfCerts cfs (embed4proof.sl), for the css of red/chunks.sl.
; cfs-run decodes cfs again from chunk-srcs, for a native job. Load after evalid.sl, triad.sl, trivfive.sl, inductfc.sl
; and red/chunks.sl, in the chain PLAN.md gives.

(let ((many cfs) (erased cl)) (concat-c css))

(def-fns _ $ (erased concat-fn : (erased (List (List (Config))) ks) (erased (List (Config)) a b) (subterm erased (ConcatL ks a) p)
    (erased (ConcatL ks b) q) -> (erased (Eq (List (Config)) a b) e))
  (match erased p _
    ((CLNil) (let-match erased q (CLNil)) (Refl _ a))
    ((CLSkip ks1 _ p1) (let-match erased q (CLSkip _ _ q1)) (let-match erased (concat-fn ks1 _ _ p1 q1) (Refl _ _)) (Refl _ a))
    ((CLCons _ cs cfs1 ks1 p1) (let-match erased q (CLCons _ _ cfs2 _ q1)) (let-match erased (concat-fn (Cons _ cs ks1) cfs1 cfs2 p1 q1) (Refl _ _))
      (Refl _ a))))

(def-fns _ $ (many cfs-run : -> (many (List (Config)) c) (many (Checked (Eq (List (Config)) c cfs)) e))
  (let-match many (decode-all chunk-srcs) (POk _ _ _ _ d _ da) (else (values (Nil _) (ChkNo _))))
  (let-match erased (decall-fn chunk-srcs _ _ d css da css-dec) (Refl _ _))
  (let ((many c) (erased cl1)) (concat-c d))
  (values c (ChkYes _ (concat-fn css c cfs cl1 cl))))

(def-fns _ $ (erased four-color-open : (erased (UnavE cfs) u) (erased (AllRedC CRX css) ar) (erased (BirkhoffChecks) bks) (erased (CfCerts cfs) ccx)
    -> (erased (FourColor) r))
  (four-color-from (embed-analysis CRX css cfs cl ar u (birk-geo-of bks) (not-embed cfs bks (full-red-of bks (triv-red-of triv-five)) ccx (embed-valid bks) triad-five))))
