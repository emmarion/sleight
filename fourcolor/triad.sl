; triad_valid of contract.v with minimality as data, and the parts of birkhoff.v's SpokeRing section it uses, for faces of any
; size: the face of a dart read with the labels of its spokes, chordless_spoke_ring, adj12_edge and fcard_adj_max. Load after
; contract3.sl, in its chain. Faces are read through a FaceLab labelling throughout. That these statements match Coq's has been
; checked only by reading.

(def-fns _ $ (erased orbit-walk : (erased (Nat) x a b) (erased (List (Nat)) f os s ws) (erased (Orbit f x os) o) (subterm erased (Path f s a b ws) w)
    (erased (In a os) ia) -> (erased (In b os) r))
  (let-match erased w (PathStep _ _ ws1 _ a1 _ pa _ w1) ((PathHere _ _ _) ia))
  (let ((erased o2)) o)
  (let-match erased o2 (MkOrbit _ xs _ y px wo))
  (orbit-walk x a1 b f os s ws1 o w1 (match erased ia (((In a1 os) r))
    ((InHere _ _) (let-match erased (nth-fn _ f x y a1 px pa) (Refl _ _)) (path-start-in f _ xs y x wo))
    ((InThere _ _ _ ia1) (path-next f _ xs y x a a1 wo ia1 pa)))))

; Every dart on the face of x is on its orbit.
(def-fns _ $ (erased orbit-in : (erased (Nat) x u) (erased (List (Nat)) f os) (erased (Orbit f x os) o) (erased (SomePath f (Nil (Nat)) x u) sp)
    -> (erased (In u os) r))
  (let ((erased o2)) o)
  (let-match erased o2 (MkOrbit _ xs _ y px wo))
  (let-match erased sp (MkSomePath _ _ ws _ _ w))
  (orbit-walk x x u f os (Nil _) ws o w (InHere x xs)))

(def-fns _ $ (erased orbit-lab : (erased (Nat) x l) (erased (List (Nat)) f lab os) (erased (Orbit f x os) o) (erased (Respects lab f lab) rf)
    (erased (Nth (Nat) lab x l) pl) -> (erased (LabAll lab l os) r))
  (let-match erased o (MkOrbit _ xs _ y px w))
  (LabCons lab xs l x pl (walk-laball y x l f lab _ xs w rf (respects-nth lab f lab x y l rf px pl))))

; The face of x, of label lx and k darts: its orbit Vs from x, and ls the labels of the faces of its spokes, distinct.
(def-adts $ (FRec : ((Nat) d) ((List (Nat)) e n f fe lab) ((Nat) x lx k) ((List (Nat)) Vs ls) -> Type)
  enum
  (many MkFRec : (erased (Nat) d x lx k) (erased (List (Nat)) e n f fe lab Vs Rs ls) (erased (Orbit f x Vs) o) (erased (Length (Nat) Vs k) lv)
      (erased (Distinct Vs) dv) (erased (LabAll lab lx Vs) al) (erased (Respects fe Vs Rs) rv) (erased (Respects lab Rs ls) rl) (erased (Distinct ls) dl)
      (erased (Nth (Nat) lab x lx) plx) -> (FRec d e n f fe lab x lx k Vs ls)))

; The face of x read with its spokes, or a reduction from double-dart (scycle_spoke_ring for a face of any size).
(def-fns _ $ (erased fr-make : (erased (Level) B) (erased (Nat) d x k) (erased (List (Nat)) e n f fe lab) (erased (MinCx B d e n f fe lab) m)
    (erased (Order f x k) o) -> (erased (Nat) lx) (erased (List (Nat)) Vs ls) (erased (HOr (FRec d e n f fe lab x lx k Vs ls) (Reduces B d e n f)) r))
  (let ((erased m2)) m)
  (let-match erased m2 (MkMinCx _ _ _ _ _ _ _ pb bks c cn nc))
  (let ((erased c2)) c)
  (let-match erased c2 (MkSpk _ _ _ _ _ _ ids h gen bl pl cu rfe kfe io ufe lfe fl rl))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ll)) (respects-length lab f lab d rl lf))
  (let-match erased o (MkOrder _ xs _ y k1 py w lxs))
  (let ((erased lx) (erased ly)) (values (pre-lt d x y f fi pmf py) (perm-val d x y f fi pmf py)))
  (let ((erased uxs) (erased _)) (path-under d y x f fi _ xs pmf w ly))
  (let ((erased Vs)) (Cons _ x xs))
  (let ((erased Rs) (erased rv)) (respects-exists fe Vs d (UnderCons xs x d lx uxs) lfe))
  (let ((erased l) (erased plx)) (nth-exists _ lab d x ll lx))
  (let ((erased ls) (erased rls)) (respects-exists lab Rs d (respects-under-vals fe Vs Rs d rv ufe) ll))
  (let ((erased ob)) (MkOrbit f xs x y py w))
  (let ((erased al)) (orbit-lab x l f lab Vs ob rl plx))
  (let ((erased dv)) (DistCons x xs (path-avoid f _ xs y x x w (InHere x _)) (walk-distinct f (Nil _) xs y x w)))
  (let-match erased (spokes-simple B d l e n f fe lab Vs Rs ls m rv rls dv al) (OrL _ _ dl) ((OrR _ _ r) (values l Vs ls (OrR _ _ r))))
  (values l Vs ls (OrL _ _ (MkFRec d x l k e n f fe lab Vs Rs ls ob (LengthCons _ x xs k1 lxs) dv al rv rls dl plx))))

; A dart u on the face of x has the label of the face of its edge image in ls.
(def-fns _ $ (erased fr-hit : (erased (Nat) d x lx k u eu l) (erased (List (Nat)) e n f fe lab Vs ls) (erased (FRec d e n f fe lab x lx k Vs ls) fr)
    (erased (Spk d e n f fe lab) c) (erased (Nth (Nat) lab u lx) pu) (erased (Nth (Nat) e u eu) pe) (erased (Nth (Nat) lab eu l) pl) -> (erased (In l ls) r))
  (let-match erased fr (MkFRec _ _ _ _ _ _ _ _ _ _ Rs _ o lv dv al rv rl dl plx))
  (let ((erased c2)) c)
  (let-match erased c2 (MkSpk _ _ _ _ _ _ ids h gen bl pl0 cu rfe kfe io ufe lfe fl rlf))
  (let ((erased s) (erased ps) (erased is)) (respects-val fe Vs Rs u rv (orbit-in x u f Vs o (facelab-same d x u lx f lab fl plx pu))))
  (let ((erased eu2) (erased pe2) (erased pf)) (fe-split d u s e n f fe lab c ps))
  (let-match erased (nth-fn _ e u eu eu2 pe pe2) (Refl _ _))
  (in-map lab Rs ls s l is rl (respects-nth lab f lab eu s l rlf pf pl)))
