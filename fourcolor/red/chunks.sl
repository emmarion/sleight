; css, the chunks of configs.sl decoded from config-srcs (css-dec its DecAll). A check P of a chunk's string gives a
; (Decoded P s), and on-chunks turns one for each string into P of each chunk of css, so that a native job need hold only
; the chunk's string. Load after configs.sl.

(comptime-match many (decode-all config-srcs) (POk _ _ _ _ css _ css-dec))

(def-adts $ (Decoded : ((TyCtor ((List (Config)) cs) -> Type) P) ((String) s) -> Type)
  enum
  (many MkDecoded : (erased (TyCtor ((List (Config)) cs) -> Type) P) (erased (String) s e) (erased (List (Config)) cs) (erased (DCfgs s cs e) d)
      (erased (P cs) a) -> (Decoded P s)))

(def-adts $ (OnSrcs : ((TyCtor ((List (Config)) cs) -> Type) P) ((List (String)) ss) -> Type)
  enum
  (many OSNil : (erased (TyCtor ((List (Config)) cs) -> Type) P) -> (OnSrcs P (Nil (String))))
  (many OSCons : (erased (TyCtor ((List (Config)) cs) -> Type) P) (erased (String) s) (erased (List (String)) ss) (erased (Decoded P s) a)
      (erased (OnSrcs P ss) r) -> (OnSrcs P (Cons (String) s ss))))

(def-adts $ (OnChunks : ((TyCtor ((List (Config)) cs) -> Type) P) ((List (List (Config))) css) -> Type)
  enum
  (many OCNil : (erased (TyCtor ((List (Config)) cs) -> Type) P) -> (OnChunks P (Nil (List (Config)))))
  (many OCCons : (erased (TyCtor ((List (Config)) cs) -> Type) P) (erased (List (Config)) cs) (erased (List (List (Config))) css) (erased (P cs) a)
      (erased (OnChunks P css) r) -> (OnChunks P (Cons (List (Config)) cs css))))

(def-fns _ $ (erased on-chunks : (erased (TyCtor ((List (Config)) cs) -> Type) P) (erased (List (String)) ss r) (erased (List (List (Config))) css)
    (subterm erased (DecAll ss css r) da) (erased (OnSrcs P ss) o) -> (erased (OnChunks P css) c))
  (match erased da _
    ((DANil) (OCNil P))
    ((DACons s ss1 _ cs css1 _ d da1)
      (let-match erased o (OSCons _ _ _ a o1))
      (let-match erased a (MkDecoded _ _ _ cs2 d2 pa))
      (let ((erased ec) (erased _)) (dcfgs-fn s _ _ cs2 cs d2 d))
      (let-match erased ec (Refl _ _))
      (OCCons P cs css1 pa (on-chunks P ss1 r css1 da1 o1)))))
