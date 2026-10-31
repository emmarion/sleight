(def-adts $ (SplitW : ((Nat) d) ((List (Nat)) e n f) ((List (Mp)) ms) -> Type)
  enum
  (many MkSplitW : (erased (Nat) d dd dr) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr)
      (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr (Nil (Nat)) (Nil (Nat))) pt)
      -> (SplitW d e n f (Cons (Mp) (MkMp dd ed nd fd) $ Cons (Mp) (MkMp dr er nr fr) $ Nil (Mp)))))

(def-fns _ $ (erased split-glue : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Mp)) ms) (erased (SplitW d e n f ms) w)
    (erased (MpCols ms) cs) -> (erased (List (Nat)) ks) (erased (FourColoring e f ks) c))
  (let-match erased w (MkSplitW _ dd dr _ _ _ ed nd fd er nr fr hd hr pt))
  (let-match erased cs (MpcCons _ _ _ _ kd _ cd cs1))
  (let-match erased cs1 (MpcCons _ _ _ _ kr _ cr _))
  (patch-colorable-nil d dd dr e n f ed nd fd er nr fr hd hr kd kr pt cd cr))

(def-fns _ $ (erased split-reduces : (erased (Level) B) (erased (Predates (Level) (level-of split-glue) B) pb) (erased (Nat) d)
    (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) (erased (Lt (Zero) d) ld) -> (erased (HOr (Connected d e n f) (Reduces B d e n f)) r))
  (let-match erased p (MkPbpp _ _ _ _ hm gen bl pl pc))
  (let-match erased (gcomp-split d e n f hm gen bl pl pc ld) (OrR _ _ sp) ((OrL _ _ conn) (OrL _ _ conn)))
  (let-match erased sp (MkGcompSplit _ dd dr _ _ _ ed nd fd er nr fr hd hr pt gd bd pld pcd ltd gr br plr pcr ltr))
  (let ((erased pt2)) pt)
  (let-match erased pt2
    (MkPatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ids idd idr bG bGr h hmd hmr io iod ior lhd lhr dhd dhr uhd uhr cyd sd cyr dbr rbd rbr rv pp med mnd mer mnr))
  (let ((erased ms)) (Cons (Mp) (MkMp dd ed nd fd) $ Cons (Mp) (MkMp dr er nr fr) $ Nil (Mp)))
  (OrR _ _ (MkReduces B d e n f ms
    (SmallerCons d dd ed nd fd _ (MkPbpp dd ed nd fd hmd gd bd pld pcd) ltd $ SmallerCons d dr er nr fr _ (MkPbpp dr er nr fr hmr gr br plr pcr) ltr $ SmallerNil d)
    (MkColorFrom B (level-of split-glue) d e n f ms SplitW (MkSplitW d dd dr e n f ed nd fd er nr fr hd hr pt) pb split-glue))))
