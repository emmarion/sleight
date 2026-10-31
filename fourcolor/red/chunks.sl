(def-adts $ (Decoded : ((TyCtor ((List (Config)) cs) -> Type) P) ((List (String)) ss) -> Type)
  enum
  (many MkDecoded : (erased (TyCtor ((List (Config)) cs) -> Type) P) (erased (List (String)) ss e) (erased (List (Config)) cs) (erased (DecList ss cs e) d)
      (erased (P cs) a) -> (Decoded P ss)))

(def-adts $ (OnSrcs : ((TyCtor ((List (Config)) cs) -> Type) P) ((List (List (String))) sss) -> Type)
  enum
  (many SrcNil : (erased (TyCtor ((List (Config)) cs) -> Type) P) -> (OnSrcs P (Nil (List (String)))))
  (many SrcCons : (erased (TyCtor ((List (Config)) cs) -> Type) P) (erased (List (String)) ss) (erased (List (List (String))) sss) (erased (Decoded P ss) a)
      (erased (OnSrcs P sss) r) -> (OnSrcs P (Cons (List (String)) ss sss))))

(def-adts $ (OnChunks : ((TyCtor ((List (Config)) cs) -> Type) P) ((List (List (Config))) css) -> Type)
  enum
  (many OnNil : (erased (TyCtor ((List (Config)) cs) -> Type) P) -> (OnChunks P (Nil (List (Config)))))
  (many OnCons : (erased (TyCtor ((List (Config)) cs) -> Type) P) (erased (List (Config)) cs) (erased (List (List (Config))) css) (erased (P cs) a)
      (erased (OnChunks P css) r) -> (OnChunks P (Cons (List (Config)) cs css))))

(def-fns _ $ (erased on-chunks : (erased (TyCtor ((List (Config)) cs) -> Type) P) (erased (List (List (String))) sss r) (erased (List (List (Config))) css)
    (subterm erased (DecAll sss css r) da) (erased (OnSrcs P sss) o) -> (erased (OnChunks P css) c))
  (let-match erased da (DACons ss _ sss1 _ cs css1 d da1) ((DANil) (OnNil P)))
  (let-match erased o (SrcCons _ _ _ a o1))
  (let-match erased a (MkDecoded _ _ _ cs2 d2 pa))
  (let-match erased (declist-fn ss _ _ cs2 cs d2 d) (Refl _ _))
  (OnCons P cs css1 pa (on-chunks P sss1 r css1 da1 o1)))

(let ((many chunk-sizes) (erased _)) (repeat _ 31 20))
(let ((many chunk-srcs) (erased chunk-flat)) (cut-at _ chunk-sizes config-srcs))
(comptime-match many (decode-all chunk-srcs) (POk _ _ _ _ css _ css-dec))
