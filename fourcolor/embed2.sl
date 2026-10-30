; First-order pieces of not_embed_reducible of embed.v: colourings carried through the patch that embed_patch builds.
; Load after embed.sl, in its chain.

; Each dart of ys is reached from the dart of xs at the same position along f (cface, read as f steps forward).
(def-adts $ (Reach : ((List (Nat)) f xs ys) -> Type)
  enum
  (many ReachNil : (erased (List (Nat)) f) -> (Reach f (Nil (Nat)) (Nil (Nat))))
  (many ReachCons : (erased (List (Nat)) f xs ys) (erased (Nat) x y) (erased (SomePath f (Nil (Nat)) x y) w) (erased (Reach f xs ys) rest)
      -> (Reach f (Cons (Nat) x xs) (Cons (Nat) y ys))))

(def-fns _ $ (erased path-col : (erased (List (Nat)) ks f s xs) (erased (Nat) x y l) (erased (Respects ks f ks) rf) (subterm erased (Path f s x y xs) w)
    (erased (Nth (Nat) ks x l) px) -> (erased (Nth (Nat) ks y l) r))
  (let-match erased w (PathStep _ _ xs1 _ z _ pz _ w1) ((PathHere _ _ _) px))
  (path-col ks f s xs1 z y l rf w1 (respects-nth ks f ks x z l rf pz px)))

(def-fns _ $ (erased reach-resp : (erased (List (Nat)) ks f xs ys L) (erased (Respects ks f ks) rf) (subterm erased (Reach f xs ys) rc)
    (erased (Respects ks xs L) rx) -> (erased (Respects ks ys L) r))
  (let-match erased rc (ReachCons _ xs1 ys1 x y w rc1) ((ReachNil _) (let-match erased rx (RespNil _)) (RespNil ks)))
  (let-match erased rx (RespCons _ _ L1 _ l p rx1))
  (let-match erased w (MkSomePath _ _ ps _ _ pa))
  (RespCons ks ys1 L1 y l (path-col ks f (Nil _) ps x y l rf pa p) (reach-resp ks f xs1 ys1 L1 rf rc1 rx1)))

(def-fns _ $ (erased differ-resp : (erased (List (Nat)) ke ks h A B) (erased (Differ ke ks) df) (subterm erased (Respects ke h A) ra)
    (erased (Respects ks h B) rb) -> (erased (Differ A B) r))
  (let-match erased ra (RespCons _ h1 A1 j a pa ra1) ((RespNil _) (let-match erased rb (RespNil _)) (DifferNil)))
  (let-match erased rb (RespCons _ _ Bt _ b pb rb1))
  (DifferCons A1 Bt a b (differ-nth ke ks j a b df pa pb) (differ-resp ke ks h1 A1 Bt df ra1 rb1)))

; A four-colouring ks of (e, f) gives the four-colouring ks . h of (e2, f2) when h sends the face and edge images of each dart
; of (e2, f2) to darts reached along f from the face and edge images of its image (the colouring kc . embd of not_embed_reducible).
(def-fns _ $ (erased pull-col : (erased (Nat) d d2) (erased (List (Nat)) e f e2 f2 h ks hf2 eh he2 kd) (erased (FourColoring e f ks) c)
    (erased (Length (Nat) e d) le) (erased (Length (Nat) ks d) lk) (erased (Under e d) ue) (erased (Length (Nat) h d2) lh)
    (erased (Respects h f2 hf2) r1) (erased (Reach f h hf2) rc1) (erased (Respects e h eh) r2) (erased (Respects h e2 he2) r3) (erased (Reach f eh he2) rc2)
    (erased (Respects ks h kd) rk) -> (erased (FourColoring e2 f2 kd) r))
  (let-match erased c (MkFourColoring _ _ _ ke rf re df u))
  (let ((erased lkd)) (respects-length ks h kd d2 rk lh))
  (let ((erased A) (erased rA)) (respects-exists ks eh d (respects-under-vals e h eh d r2 ue) lk))
  (MkFourColoring e2 f2 kd A
    (respects-assoc f2 h ks hf2 kd kd d2 r1 (reach-resp ks f h hf2 kd rf rc1 rk) rk lkd lh)
    (respects-assoc e2 h ks he2 kd A d2 r3 (reach-resp ks f eh he2 A rf rc2 rA) rk lkd lh)
    (differ-resp ke ks h A kd df (respects-assoc h e ks eh ke A d r2 rA re (respects-length ks e ke d re le) le) rk)
    (respects-under-vals ks h kd 4 rk u)))

; The last step of not_embed_reducible: a patch of the map from a disk map whose darts embd sends into a configuration map
; (ec, fc) as pull-col asks, with its ring bd sent to erc, a four-colouring kc of the configuration map whose colours on erc
; have the trace et, and a ring trace rot 1 (rev et) of the remainder map on br, give a four-colouring of the map.
(def-fns _ $ (erased embed-color : (erased (Nat) d dd dr dc) (erased (List (Nat)) e n f ed nd fd er nr fr hd hr bd br ec fc kc embd q1 q2 q3 erc lc)
    (erased (List (Col)) cs et et2) (erased (Patch d dd dr e n f ed nd fd er nr fr hd hr bd br) pt) (erased (FourColoring ec fc kc) c)
    (erased (Length (Nat) ec dc) le) (erased (Length (Nat) kc dc) lk) (erased (Under ec dc) ue) (erased (Length (Nat) embd dd) lh) (erased (Under embd dc) uh)
    (erased (Respects embd fd q1) r1) (erased (Reach fc embd q1) rc1) (erased (Respects ec embd q2) r2) (erased (Respects embd ed q3) r3)
    (erased (Reach fc q2 q3) rc2) (erased (Respects embd bd erc) rb) (erased (Respects kc erc lc) rl) (erased (All2 (Nat) (Col) ColOf lc cs) co)
    (erased (Trace cs et) t) (erased (RotRev et et2) rr) (erased (RingTrace er fr br et2) tr) -> (erased (List (Nat)) ks) (erased (FourColoring e f ks) r))
  (let ((erased kd) (erased rk)) (respects-exists kc embd dc uh lk))
  (let ((erased cd)) (pull-col dc dd ec fc ed fd embd kc q1 q2 q3 kd c le lk ue lh r1 rc1 r2 r3 rc2 rk))
  (let ((erased rlb)) (respects-assoc bd embd kc erc kd lc dd rb rl rk (respects-length kc embd kd dd rk lh) lh))
  (patch-colorable d dd dr e n f ed nd fd er nr fr hd hr bd br et et2 pt (MkRingTrace ed fd bd kd lc cs et cd rlb co t) rr tr))
