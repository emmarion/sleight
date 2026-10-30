; Unavoidability in the shape of unavoidability.v, with the embedding of quiz.v: in every plain cubic connected pentagonal
; map of genus 0, a configuration of red/configs.sl has a preembedding of its kernel into the map or its mirror (CfEmbed).
; One compiled run builds the quiz tree with its evidence (qtree.sl), and does the certified walks and cap checks of
; unavgoal.sl and the certified redpart of redc.sl on every obligation. Load after qmirror.sl and data.sl.

(def-adts $ (AllRed : ((Qzt) qt) ((List (List (Sub))) obl) -> Type)
  enum
  (many ARNil : (erased (Qzt) qt) -> (AllRed qt (Nil (List (Sub)))))
  (many ARCons : (erased (Qzt) qt) (erased (List (Sub)) q) (erased (List (List (Sub))) rest) (erased (RedD qt q) dd) (erased (AllRed qt rest) r)
      -> (AllRed qt (Cons (List (Sub)) q rest))))

(def-adts $ (AllRedW : ((Qzt) qt) ((List (List (List (Sub)))) wobl) -> Type)
  enum
  (many AWNil : (erased (Qzt) qt) -> (AllRedW qt (Nil (List (List (Sub))))))
  (many AWCons : (erased (Qzt) qt) (erased (List (List (Sub))) obl) (erased (List (List (List (Sub)))) rest) (erased (AllRed qt obl) a)
      (erased (AllRedW qt rest) r) -> (AllRedW qt (Cons (List (List (Sub))) obl rest))))

(def-fns _ $ (erased allred-mem : (erased (Qzt) qt) (erased (List (List (Sub))) obl) (erased (List (Sub)) q) (subterm erased (AllRed qt obl) a)
    (erased (Mem (List (Sub)) q obl) m) -> (erased (RedD qt q) r))
  (let-match erased a (ARCons _ q1 rest dd a1) (absurd (ARNil _) m))
  (match erased m _
    ((MemHere _ _ _) dd)
    ((MemThere _ _ _ _ m1) (allred-mem qt rest q a1 m1))))

(def-fns _ $ (erased allredw-nth : (erased (Qzt) qt) (erased (List (List (List (Sub)))) wobl) (erased (Nat) i) (erased (List (List (Sub))) obl)
    (subterm erased (AllRedW qt wobl) a) (erased (Nth (List (List (Sub))) wobl i obl) pn) -> (erased (AllRed qt obl) r))
  (let-match erased a (AWCons _ o1 rest a0 a1) (absurd (AWNil _) pn))
  (let-match erased pn (NthThere _ _ _ i1 _ pn1) ((NthHere _ _ _) a0))
  (allredw-nth qt rest i1 obl a1 pn1))

(def-fns _ $ (many allred-c : (many (Qzt) qt) (subterm many (List (List (Sub))) obl) -> (many (Bool) ok) (erased (IfT ok (AllRed qt obl)) w))
  (let-match many obl (Cons _ q rest) ((Nil _) (values (BTrue) (IfY _ (ARNil qt)))))
  (let ((many ok1) (erased w1)) (redp-c qt q))
  (let-match many ok1 (BTrue) ((BFalse) (values (BFalse) (IfF _))))
  (let ((many ok2) (erased w2)) (notail $ allred-c qt rest))
  (let-match many ok2 (BTrue) ((BFalse) (values (BFalse) (IfF _))))
  (let-match erased w1 (IfY _ dd))
  (let-match erased w2 (IfY _ a))
  (values (BTrue) (IfY _ (ARCons qt q rest dd a))))

(def-fns _ $ (many allredw-c : (many (Qzt) qt) (subterm many (List (List (List (Sub)))) wobl) -> (many (Bool) ok) (erased (IfT ok (AllRedW qt wobl)) w))
  (let-match many wobl (Cons _ obl rest) ((Nil _) (values (BTrue) (IfY _ (AWNil qt)))))
  (let ((many ok1) (erased w1)) (allred-c qt obl))
  (let-match many ok1 (BTrue) ((BFalse) (values (BFalse) (IfF _))))
  (let ((many ok2) (erased w2)) (notail $ allredw-c qt rest))
  (let-match many ok2 (BTrue) ((BFalse) (values (BFalse) (IfF _))))
  (let-match erased w1 (IfY _ a1))
  (let-match erased w2 (IfY _ a2))
  (values (BTrue) (IfY _ (AWCons qt obl rest a1 a2))))

; The map itself, or its mirror (hyper-mirror of hyprelabel.sl).
(def-adts $ (MapOrMirror : ((Nat) d) ((List (Nat)) e n f e2 n2 f2) -> Type)
  enum
  (many MoSame : (erased (Nat) d) (erased (List (Nat)) e n f) -> (MapOrMirror d e n f e n f))
  (many MoMirror : (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (Respects f n fn) rfn) (erased (HPerm d n ni) pn) (erased (HPerm d f fi) pf)
      -> (MapOrMirror d e n f fn ni fi)))

; A configuration of cfs, with its map (ec, nc, fc), ring rc and arities ksc as cpmap.sl builds them, has a preembedding
; h of its kernel as into the map (em, nm, fm) or its mirror, sending x0c to x0m.
(def-adts $ (CfEmbed : ((List (Config)) cfs) ((Nat) dm) ((List (Nat)) em nm fm ksm) -> Type)
  enum
  (many MkCfEmbed : (erased (List (Config)) cfs) (erased (Bool) sym) (erased (List (Nat)) cci) (erased (List (Step)) cp) (erased (Nat) dm dc x0c x0m)
      (erased (List (Nat)) em nm fm ksm em2 nm2 fm2 ec nc fc rc ksc as hl) (erased (Mem (Config) (MkConfig sym cci cp) cfs) m) (erased (Cpmap cp dc ec fc rc) c)
      (erased (PointedMap dc ec nc fc rc) pm) (erased (OrderList dc fc ksc) ol) (erased (MapOrMirror dm em nm fm em2 nm2 fm2) mo) (erased (Geo dm em2 nm2 fm2 ksm) g2)
      (erased (KernelList dc fc rc as) kl) (erased (Preembedding ec nc fc ksc em2 fm2 ksm as hl) pe) (erased (Nth (Nat) hl x0c x0m) h0) (erased (Lt x0m dm) lx)
      -> (CfEmbed cfs dm em nm fm ksm)))

(def-fns _ $ (erased hit-embed : (erased (List (Config)) cfs) (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g)
    (erased (QzHit cfs d e n ks) hit) -> (erased (CfEmbed cfs d e n f ks) r))
  (let-match erased hit (MkQzHit _ _ y _ _ _ cf qz qz2 m c v fz ly))
  (let-match erased c (MkCfQz sym cci cp dc x0c ec nc fc rc ksc _ cm pm qc))
  (let-match erased qc (MkQzCert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ olc _ _ _ _ _ _ _ _ _))
  (match erased v _
    ((VSame _)
      (let ((erased as) (erased hl) (erased kl) (erased pe) (erased h0)) (quiz-preembedding dc x0c d y ec nc fc ksc rc e n f ks qz qc g ly fz))
      (MkCfEmbed cfs sym cci cp d dc x0c y e n f ks e n f ec nc fc rc ksc as hl m cm pm olc (MoSame d e n f) g kl pe h0 ly))
    ((VFlip _ _ fl)
      (let ((erased fn) (erased ni) (erased fi) (erased g2) (erased rfn) (erased pn) (erased pf)) (geo-mirror d e n f ks g))
      (let ((erased w) (erased fz2) (erased lw)) (fitz-flip d y e n f ks fn ni qz qz2 g rfn pn ly fl fz))
      (let ((erased as) (erased hl) (erased kl) (erased pe) (erased h0)) (quiz-preembedding dc x0c d w ec nc fc ksc rc fn ni fi ks qz qc g2 lw fz2))
      (MkCfEmbed cfs sym cci cp d dc x0c w e n f ks fn ni fi ec nc fc rc ksc as hl m cm pm olc (MoMirror d e n f fn ni fi rfn pn pf) g2 kl pe h0 lw))))

(def-adts $ (UnavE : ((List (Config)) cfs) -> Type)
  enum
  (many MkUnavE : (erased (List (Config)) cfs) (erased (Level) lv)
      (erased (Fn lv (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Connected d e n f) cc)
          (erased (Genus d e n f (Zero)) gen) -> (erased (CfEmbed cfs d e n f ks) r)) every)
      -> (UnavE cfs)))

(let ((many drs)) (symmetrize (base-drules)))

(let ((many cfs)) (concat-cfs (config-chunks)))

(goal erased (UnavE cfs))

(def-fns _ $ (many unave-run : -> (many (Checked (UnavE cfs)) r))
  (let ((many qt) (many qc)) (quiz-tree-c cfs))
  (let-match many qc (ChkYes _ qi) ((ChkNo _) (ChkNo _)))
  (let ((many sok) (erased sw)) (small-c drs))
  (let-match many sok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many wok) (many wobl) (erased ww))
    (walk-c drs 5 12 (Cons _ (script5) $ Cons _ (script6) $ Cons _ (script7) $ Cons _ (script8) $ Cons _ (script9) $ Cons _ (script10) $
      Cons _ (script11) $ Nil _)))
  (let-match many wok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many cok) (many cobl) (erased cw)) (cap-c drs (Nil _) 5 9 4))
  (let-match many cok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many rwok) (erased rw)) (allredw-c qt wobl))
  (let-match many rwok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many rcok) (erased rc)) (allred-c qt cobl))
  (let-match many rcok (BTrue) ((BFalse) (ChkNo _)))
  (let-match erased sw (IfY _ sm))
  (let-match erased ww (IfY _ wl))
  (let-match erased cw (IfY _ cl))
  (let-match erased rw (IfY _ aw))
  (let-match erased rc (IfY _ ac))
  (def-fns _ $ (erased every : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Connected d e n f) cc)
      (erased (Genus d e n f (Zero)) gen) -> (erased (CfEmbed cfs d e n f ks) r))
    (let ((erased x) (erased pos) (erased neg) (erased lx) (erased dsc) (erased lt)) (posz-dscore d e n f ks drs g cc gen))
    (let ((erased (HasFit d e n ks qt) hf))
      (match erased (unav-dart d x pos neg e n f ks drs (Nil _) cobl wobl sm wl cl g lx dsc lt) _
        ((UWalk _ _ _ i _ _ _ _ _ obl _ _ pn h)
          (let-match erased h (MkMapHit _ z _ _ _ q _ lz m ex))
          (red-sound d z e n f ks qt q (allred-mem qt obl q (allredw-nth qt wobl i obl aw pn) m) g lz ex))
        ((UCap _ _ _ _ _ _ _ _ _ _ h)
          (let-match erased h (MkMapHit _ z _ _ _ q _ lz m ex))
          (red-sound d z e n f ks qt q (allred-mem qt cobl q ac m) g lz ex))))
    (hit-embed cfs d e n f ks g (qzt-hit cfs d e n f ks qt qi g hf)))
  (ChkYes _ (MkUnavE cfs (level-of every) every)))

(let ((many res)) (native-compute unave-run))
(comptime-match many res (ChkYes _ u))
(qed u)
