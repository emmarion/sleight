; expect: 0
(def-fns _ $ (many f : (erased (Nat) n) (erased n is _m at n) -> ) (values))
(def-fns _ $ (many k : (erased (Nat) a) (erased (Nat) b) (erased (Eq (Nat) a b) _p) (erased (Nat) d at b) (erased (Eq (Nat) a d) _q) -> ) (values))
(def-fns _ $ (many h : (erased (Nat) n) (erased (Slot) t) (erased (Eq (Slot) t (slot-of n)) _q) (erased (Eq (Nat) n n) _p) -> (erased t is u)) t)
(def-fns _ $ (many same : (erased (Slot) a) (erased (Slot) b) (erased (Eq (Slot) a b) _p) -> ) (values))
(def-lvl M)
(def-fns _ $ (many shadow : (erased (Nat) n) (erased n is _o) (erased (Fn M (erased (Nat) n) (erased (Nat) m at n) -> (erased (slot-of n) is s)) _g) -> ) (values))
(def-fns M $ (erased e : (erased (Nat) n) (erased (Nat) _m at n) -> (erased (slot-of n) is s)) (slot-of n))
(let ((erased x)) 3)
(let () (f x x))
(let () (k x x (Refl _ x) x (Refl _ x)))
(let () (k _ x (Refl _ x) x (Refl _ x)))
(let ((erased u)) (h x _ (Refl _ _) (Refl _ x)))
(let () (same u (slot-of x) (Refl _ u)))
(let () (shadow _ x e))
0
; warns: tests/at_target_wild.sl:7:77: warning: declaration of `n` shadows a previous binder
; warns: tests/at_target_wild.sl:7:29: note: shadowed binder is here
