(let ((many cfs) (erased cl)) (concat-c css))

(def-fns _ $ (erased concat-fn : (erased (List (List (Config))) ks) (erased (List (Config)) a b) (subterm erased (ConcatL ks a) p)
    (erased (ConcatL ks b) q) -> (erased (Eq (List (Config)) a b) e))
  (match erased p _
    ((ConcatNil) (let-match erased q (ConcatNil)) (Refl _ a))
    ((ConcatSkip ks1 _ p1) (let-match erased q (ConcatSkip _ _ q1)) (let-match erased (concat-fn ks1 _ _ p1 q1) (Refl _ _)) (Refl _ a))
    ((ConcatCons _ cs cfs1 ks1 p1) (let-match erased q (ConcatCons _ _ cfs2 _ q1)) (let-match erased (concat-fn (Cons _ cs ks1) cfs1 cfs2 p1 q1) (Refl _ _))
      (Refl _ a))))

(def-fns _ $ (many cfs-run : -> (many (List (Config)) c) (many (Checked (Eq (List (Config)) c cfs)) e))
  (let-match many (decode-all chunk-srcs) (POk _ _ _ _ d _ da) (else (values (Nil _) (ChkNo _))))
  (let-match erased (decall-fn chunk-srcs _ _ d css da css-dec) (Refl _ _))
  (let ((many c) (erased cl1)) (concat-c d))
  (values c (ChkYes _ (concat-fn css c cfs cl1 cl))))

(def-fns _ $ (erased four-color-open : (erased (UnavE cfs) u) (erased (AllRedC CRX css) ar) (erased (BirkhoffChecks) bks) (erased (CfCerts cfs) cc)
    -> (erased (FourColor) r))
  (four-color-from (embed-analysis CRX css cfs cl ar u (birk-geo-of bks) (not-embed cfs bks (full-red-of bks (triv-red-of triv-five)) cc (embed-valid bks) triad-five))))
