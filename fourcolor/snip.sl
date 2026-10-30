; Cutting a planar map along a ring into a disk map and a remainder map, after snip.v. Load after sew.sl.

; x then the darts p, each on the face of the edge image of the one before, ending at y (Gonthier's path rlink).
(def-adts $ (RPath : ((List (Nat)) e f) ((Nat) x) ((List (Nat)) p) ((Nat) y) -> Type)
  enum
  (many RPNil : (erased (List (Nat)) e f) (erased (Nat) x) -> (RPath e f x (Nil (Nat)) x))
  (many RPCons : (erased (List (Nat)) e f p) (erased (Nat) x ex z y) (erased (Nth (Nat) e x ex) pe) (erased (SomePath f (Nil (Nat)) ex z) w)
      (erased (RPath e f z p y) rest) -> (RPath e f x (Cons (Nat) z p) y)))

; x :: p is a ring: a cycle of rlink on distinct faces (Gonthier's scycle rlink, for a ring that is not empty).
(def-adts $ (Ring : ((List (Nat)) e f) ((Nat) x) ((List (Nat)) p) -> Type)
  enum
  (many MkRing : (erased (List (Nat)) e f p) (erased (Nat) x y ey) (erased (RPath e f x p y) rp) (erased (Nth (Nat) e y ey) pe)
      (erased (SomePath f (Nil (Nat)) ey x) w) (erased (Simple f (Cons (Nat) x p)) s) -> (Ring e f x p)))

; A clink path from x to y leaving from no dart of r (Gonthier's path dlink).
(def-adts $ (DPath : ((List (Nat)) n f r) ((Nat) x y) -> Type)
  enum
  (many DPNil : (erased (List (Nat)) n f r) (erased (Nat) x) -> (DPath n f r x x))
  (many DPNode : (erased (List (Nat)) n f r) (erased (Nat) x y z) (erased (NotIn x r) out) (erased (Nth (Nat) n y x) pn)
      (erased (DPath n f r y z) rest) -> (DPath n f r x z))
  (many DPFace : (erased (List (Nat)) n f r) (erased (Nat) x y z) (erased (NotIn x r) out) (erased (Nth (Nat) f x y) pf)
      (erased (DPath n f r y z) rest) -> (DPath n f r x z)))

; x is in diskN r: a dlink path reaches it from the node preimage of a dart of r.
(def-adts $ (DiskN : ((List (Nat)) n f r) ((Nat) x) -> Type)
  enum
  (many MkDiskN : (erased (List (Nat)) n f r) (erased (Nat) x y y2) (erased (In y r) iy) (erased (Nth (Nat) n y2 y) pn)
      (erased (DPath n f r y2 x) dp) -> (DiskN n f r x)))

(def-fns _ $ (erased dpath-cat : (erased (List (Nat)) n f r) (erased (Nat) x y z) (subterm erased (DPath n f r x y) p) (erased (DPath n f r y z) q)
    -> (erased (DPath n f r x z) res))
  (match erased p _
    ((DPNil _ _ _ _) q)
    ((DPNode _ _ _ _ x1 _ out pn p1) (DPNode n f r x x1 z out pn (dpath-cat n f r x1 y z p1 q)))
    ((DPFace _ _ _ _ x1 _ out pf p1) (DPFace n f r x x1 z out pf (dpath-cat n f r x1 y z p1 q)))))

(def-fns _ $ (erased disk-step : (erased (List (Nat)) n f r) (erased (Nat) x y) (erased (DiskN n f r x) dn) (erased (DPath n f r x y) p)
    -> (erased (DiskN n f r y) res))
  (let-match erased dn (MkDiskN _ _ _ _ z z2 iz pn dp))
  (MkDiskN n f r y z z2 iz pn (dpath-cat n f r z2 x y dp p)))

; diskN is closed under the node preimage.
(def-fns _ $ (erased disk-pre : (erased (List (Nat)) n f r) (erased (Nat) x x2) (erased (DiskN n f r x) dn) (erased (Nth (Nat) n x2 x) pn)
    -> (erased (DiskN n f r x2) res))
  (match erased (in-dec x r) _
    ((OrL _ _ ix) (MkDiskN n f r x2 x x2 ix pn (DPNil n f r x2)))
    ((OrR _ _ ox) (disk-step n f r x x2 dn (DPNode n f r x x2 x2 ox pn (DPNil n f r x2))))))

(def-fns _ $ (erased disk-walk-pre : (erased (Nat) d a b) (erased (List (Nat)) n ni f r s xs) (erased (HPerm d n ni) pn) (subterm erased (Path ni s a b xs) w)
    (erased (DiskN n f r a) dn) -> (erased (DiskN n f r b) res))
  (let-match erased w (PathStep _ _ xs1 _ a1 _ pa _ w1) ((PathHere _ _ _) dn))
  (disk-walk-pre d a1 b n ni f r s xs1 pn w1 (disk-pre n f r a a1 dn (perm-inv d a a1 ni n (perm-sym d n ni pn) pa))))

; diskN is closed under node (diskN_node).
(def-fns _ $ (erased disk-node : (erased (Nat) d x x2) (erased (List (Nat)) n ni f r) (erased (HPerm d n ni) pn) (erased (DiskN n f r x) dn)
    (erased (Nth (Nat) n x x2) px) -> (erased (DiskN n f r x2) res))
  (let ((erased pni)) (perm-sym d n ni pn))
  (let ((erased xs) (erased w)) (cycle d x2 x ni n pni (perm-inv d x x2 n ni pn px) (perm-val d x x2 n ni pn px)))
  (disk-walk-pre d x x2 n ni f r (Nil _) xs pn w dn))

; r lies in diskN.
(def-fns _ $ (erased disk-ring : (erased (Nat) d y) (erased (List (Nat)) n ni f r) (erased (HPerm d n ni) pn) (erased (In y r) iy) (erased (Lt y d) ly)
    -> (erased (DiskN n f r y) res))
  (let ((erased y2) (erased py) (erased l2)) (perm-nth d y ni n (perm-sym d n ni pn) ly))
  (let ((erased pn2)) (perm-inv d y y2 ni n (perm-sym d n ni pn) py))
  (disk-node d y2 y n ni f r pn (MkDiskN n f r y2 y y2 iy pn2 (DPNil n f r y2)) pn2))
