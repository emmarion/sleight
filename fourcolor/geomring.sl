; Lemmas of geometry.v about lists of darts on distinct faces. Load after patch.sl.

(def-fns _ $ (erased respects-lab : (erased (List (Nat)) lab xs ls) (erased (Nat) x) (subterm erased (Respects lab xs ls) rp) (erased (In x xs) ix)
    -> (erased (Nat) l) (erased (Nth (Nat) lab x l) r))
  (let-match erased rp (RespCons _ xs1 ls1 j l pj rp1) (absurd (RespNil _) ix))
  (match erased ix _ ((InHere _ _) (values l pj)) ((InThere _ _ _ ix1) (respects-lab lab xs1 ls1 x rp1 ix1))))

; Two darts of a simple list on one face are one dart (simple_cface, and so scycle_cface).
(def-fns _ $ (erased simple-cface : (erased (List (Nat)) f p) (erased (Nat) a b) (erased (Simple f p) s) (erased (In a p) ia) (erased (In b p) ib)
    (erased (SomePath f (Nil (Nat)) a b) w) -> (erased (Eq (Nat) a b) e))
  (let-match erased s (MkSimple _ _ lab ls rf rp dl))
  (let-match erased w (MkSomePath _ _ xs _ _ pth))
  (let ((erased l) (erased pa)) (respects-lab lab p ls a rp ia))
  (simple-inj lab p ls a b l rp dl ia ib pa (path-label f lab (Nil _) xs a b l pth rf pa)))
