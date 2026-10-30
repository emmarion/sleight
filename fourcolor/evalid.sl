; embed_valid_contract of embed.v with minimality as data: notembed.sl's EmbedValid, given BirkhoffChecks, with adj11_edge of
; birkhoff.v for the triad. Load after notembed.sl. That these statements match Coq's has been checked only by reading.

; The embedding that EmbedValid takes: embed listed as h1 on the darts ids, with the facts of embed3.sl and embed5.sl.
(def-adts $ (EvCx : ((Nat) dc) ((List (Nat)) ec nc fc ksc rc) ((Nat) dm) ((List (Nat)) em nm fm ksm as hl ids h1) -> Type)
  enum
  (many MkEvCx : (erased (Nat) dc dm) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl ids h1)
      (erased (EEnv dc ec nc fc ksc rc dm em nm fm ksm as hl) en) (erased (GcOK dc ec nc rc as) ok) (erased (FunctorAll ec em as hl as) fu)
      (erased (FullAll ec em hl as as) fa) (erased (Iota dc ids) io) (erased (EmbL ec nc em nm fm as hl ids h1) el) (erased (Length (Nat) h1 dc) lh)
      -> (EvCx dc ec nc fc ksc rc dm em nm fm ksm as hl ids h1)))

; cface_h1 along a face path, read off h1 sending each face step along fm (Reach fm h1 h1f).
(def-fns _ $ (erased path-h1 : (erased (Nat) dc a b u v) (erased (List (Nat)) fc fic fm h1 h1f s xs) (erased (HPerm dc fc fic) pmf) (erased (Length (Nat) h1 dc) lh)
    (erased (Respects h1 fc h1f) rf) (erased (Reach fm h1 h1f) rc) (subterm erased (Path fc s a b xs) w) (erased (Nth (Nat) h1 a u) pu) (erased (Nth (Nat) h1 b v) pv)
    -> (erased (SomePath fm (Nil (Nat)) u v) r))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1)
    ((PathHere _ _ _) (let-match erased (nth-fn _ h1 a u v pu pv) (Refl _ _)) (MkSomePath fm (Nil _) (Nil _) u u (PathHere fm (Nil _) u))))
  (let ((erased u1) (erased pu1)) (nth-exists _ h1 dc a1 lh (perm-val dc a a1 fc fic pmf pa)))
  (some-cat fm u u1 v (reach-at fm h1 h1f a u u1 rc pu (respects-at h1 fc h1f a a1 u1 rf pa pu1))
    (path-h1 dc a1 b u1 v fc fic fm h1 h1f s xs1 pmf lh rf rc w1 pu1 pv)))

(def-fns _ $ (erased hemb-ker : (erased (List (Nat)) ec nc em nm fm as hl) (erased (Nat) x u) (erased (HEmb ec nc em nm fm as hl x u) hx) (erased (In x as) ix)
    -> (erased (Nth (Nat) hl x u) r))
  (let-match erased hx (HeK _ _ _ _ _ _ _ _ _ _ pu)
    (absurd (HeE _ _ _ _ _ _ _ _ _ _ _ ox _ _ _ _) (in-notin x as ix ox))
    (absurd (HeN _ _ _ _ _ _ _ _ _ _ _ _ _ ox _ _ _ _ _ _ _) (in-notin x as ix ox))
    (absurd (HeEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ox _ _ _ _ _ _ _ _ _ _) (in-notin x as ix ox)))
  pu)

; node keeps the darts off rc.
(def-fns _ $ (erased node-off : (erased (Nat) dc x z) (erased (List (Nat)) ec nc rc as) (erased (GcOK dc ec nc rc as) ok) (erased (Lt x dc) lx) (erased (NotIn x rc) ox)
    (erased (Nth (Nat) nc x z) pz) -> (erased (NotIn z rc) r))
  (let-match erased (gc-at dc x ec nc rc as ok lx) (MkGcAt _ _ _ _ _ ex nx pex pxe pnx rs ep cl cs))
  (let-match erased (nth-fn _ nc x z nx pz pnx) (Refl _ _))
  (let-match erased rs (RsOff _ _ _ _ _ _ onx _ _) (absurd (RsOn _ _ _ _ ix _) (in-notin x rc ix ox)))
  onx)

; cface_ac_h1, the direction the triad uses: from a kernel dart x, a face path of the map to h1 w, w off rc, follows one from x to w.
(def-fns _ $ (erased face-back : (erased (Nat) dc dm x w X W) (erased (List (Nat)) ec nc fc ksc rc em nm fm ksm as hl ids h1)
    (erased (EvCx dc ec nc fc ksc rc dm em nm fm ksm as hl ids h1) cx) (erased (In x as) ix) (erased (Lt w dc) lw) (erased (NotIn w rc) ow)
    (erased (Nth (Nat) h1 x X) px) (erased (Nth (Nat) h1 w W) pw) (erased (SomePath fm (Nil (Nat)) X W) sp) -> (erased (SomePath fc (Nil (Nat)) x w) r))
  (let-match erased cx (MkEvCx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en ok fu fa io el lh))
  (let ((erased phx)) (hemb-ker ec nc em nm fm as hl x X (embl-at dc x X ec nc em nm fm as hl ids h1 io el lh px) ix))
  (let-match erased sp (MkSomePath _ _ us _ _ p))
  (let ((erased y) (erased sy) (erased py)) (h-face-back dc dm x X W ec nc fc ksc rc em nm fm ksm as hl (Nil _) us en ix phx p))
  (let-match erased sy (MkSomePath _ _ ys _ _ pthy))
  (let ((erased iy)) (ker-path dc dm x y ec nc fc ksc rc em nm fm ksm as hl (Nil _) ys en ix pthy))
  (let-match erased (embed-inj dc dm y w W ec nc fc ksc rc em nm fm ksm as hl en ok fu fa (ker-lt dc dm y ec nc fc ksc rc em nm fm ksm as hl en iy)
      (ker-off-ring dc dm y ec nc fc ksc rc em nm fm ksm as hl en iy) lw ow (HeK ec nc em nm fm as hl y W iy py)
      (embl-at dc w W ec nc em nm fm as hl ids h1 io el lh pw)) (Refl _ _))
  sy)

; The face orbit os of x holds exactly the darts reached from x along p.
(def-fns _ $ (erased orb-step : (erased (List (Nat)) p xs) (erased (Nat) x y u v) (erased (Nth (Nat) p x y) px) (erased (Path p (Cons (Nat) x (Nil (Nat))) y x xs) w)
    (erased (In u (Cons (Nat) x xs)) iu) (erased (Nth (Nat) p u v) pv) -> (erased (In v (Cons (Nat) x xs)) r))
  (let-match erased iu (InThere _ _ _ iu1) ((InHere _ _) (let-match erased (nth-fn _ p x y v px pv) (Refl _ _)) (path-start-in p _ xs y x w)))
  (path-next p _ xs y x u v w iu1 pv))

(def-fns _ $ (erased orbit-walk : (erased (List (Nat)) p xs s ws) (erased (Nat) x y u v) (erased (Nth (Nat) p x y) px) (erased (Path p (Cons (Nat) x (Nil (Nat))) y x xs) w)
    (erased (In u (Cons (Nat) x xs)) iu) (subterm erased (Path p s u v ws) pw) -> (erased (In v (Cons (Nat) x xs)) r))
  (let-match erased pw (PathStep _ _ ws1 _ u1 _ pu _ pw1) ((PathHere _ _ _) iu))
  (orbit-walk p xs s ws1 x y u1 v px w (orb-step p xs x y u u1 px w iu pu) pw1))

(def-fns _ $ (erased orbit-in : (erased (List (Nat)) p os) (erased (Nat) x v) (erased (Orbit p x os) o) (erased (SomePath p (Nil (Nat)) x v) sp) -> (erased (In v os) r))
  (let-match erased o (MkOrbit _ xs _ y px w))
  (let-match erased sp (MkSomePath _ _ ws _ _ pw))
  (orbit-walk p xs (Nil _) ws x y x v px w (InHere x xs) pw))

(def-fns _ $ (erased path-pre : (erased (List (Nat)) p s xs) (erased (Nat) a b v) (subterm erased (Path p s a b xs) w) (erased (In v xs) iv)
    -> (erased (SomePath p (Nil (Nat)) a v) r))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1) (absurd (PathHere _ _ _) iv))
  (match erased iv _
    ((InHere _ _) (MkSomePath p (Nil _) (Nil _) a a (PathHere p (Nil _) a)))
    ((InThere _ _ _ iv1) (some-cat p a a1 v (some-step p a a1 pa) (path-pre p s xs1 a1 b v w1 iv1)))))

(def-fns _ $ (erased in-orbit : (erased (List (Nat)) p os) (erased (Nat) x v) (erased (Orbit p x os) o) (erased (In v os) iv) -> (erased (SomePath p (Nil (Nat)) x v) r))
  (let-match erased o (MkOrbit _ xs _ y px w))
  (match erased iv _
    ((InHere _ _) (MkSomePath p (Nil _) (Nil _) x x (PathHere p (Nil _) x)))
    ((InThere _ _ _ iv1) (some-cat p x y v (some-step p x y px) (path-pre p _ xs y x v w iv1)))))

(def-fns _ $ (erased orbit-exists : (erased (Nat) d x) (erased (List (Nat)) p q) (erased (HPerm d p q) pm) (erased (Lt x d) lx)
    -> (erased (List (Nat)) os) (erased (Orbit p x os) o))
  (let ((erased y) (erased py) (erased _)) (perm-nth d x p q pm lx))
  (let ((erased xs) (erased w)) (cycle d x y p q pm py lx))
  (let ((erased ys) (erased w2)) (walk-to p xs y x w))
  (values (Cons _ x ys) (MkOrbit p ys x y py w2)))
