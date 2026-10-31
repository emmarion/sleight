(def-adts $ (RedC : ((List (Config)) cs) -> Type)
  enum
  (many MkRedC : (erased (List (Config)) cs) (erased (AllRed CRX cs) p) -> (RedC cs)))

(def-fns _ $ (many red-of : (many (List (String)) ss) -> (many (Chk (Decoded RedC ss)) r))
  (let-match many (dec-list ss) (POk _ _ _ _ cs _ d) (else (CkN _)))
  (let-match many (red-all-c cs (Nil _)) (CkY _ p) ((CkN _) (CkN _)))
  (CkY _ (MkDecoded RedC ss _ cs d (MkRedC cs p))))

(def-fns _ $ (erased red-chunks : (erased (List (List (Config))) ks) (subterm erased (OnChunks RedC ks) o) -> (erased (AllRedC CRX ks) r))
  (let-match erased o (OnCons _ cs ks1 a o1) ((OnNil _) (ARCNil CRX)))
  (let-match erased a (MkRedC _ p))
  (ARCCons CRX cs ks1 p (red-chunks ks1 o1)))

(native-each pieces-red-proof piece-srcs (ss t r) (Chk (Decoded RedC ss)) (red-of ss) (CkY _ a) (SrcCons RedC ss t a r) (SrcNil RedC))
(native-then (let ((erased all-red-proof))
  (allredc-pieces CRX pcs css cfs-all pcs-cat css-cat (red-chunks pcs (on-chunks RedC piece-srcs _ pcs pcs-dec pieces-red-proof)))))
