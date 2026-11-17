(def-adts $ (Dec : ((Nat) a) ((Nat) b) -> Type)
  enum
  (many MkDec : (erased (Nat) n) -> (Dec (Succ n) n)))
(def-fns _
  ((many dec-step : (many (Nat) n) -> (many (Nat) m) (erased (Dec (Succ n) m) p)) (values n (MkDec n)))
  ((erased dec-det : (erased (Nat) n) (erased (Nat) a) (erased (Nat) b) (erased (Dec n a) p) (erased (Dec n b) q) -> (erased (Eq (Nat) a b) e))
    (let-match erased p (MkDec x))
    (let-match erased q (MkDec y))
    (Refl _ a)))
(def-fns _ $ (erased halts-of : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Nat) s) (erased (Nat) k)
    (subterm erased (RunsTo R s k) r) -> (erased (Halts R s) h))
  (match erased r _
    ((RDone _) (HDone R))
    ((RStep _ n m k1 st r1) (HStep R n m st (halts-of R m k1 r1)))))
(let ((erased L1) (many frun)) (fuel-factory (level-of dec-step) Dec dec-step))
(let ((many res)) (frun 10 3))
(comptime-match many res (FDone _ _ _ k r))
(let ((erased h)) (halts-of Dec 3 k r))
(let ((erased L2) (many brun)) (run-factory (level-of dec-step) Dec dec-step dec-det))
(let ((many k2) (erased r2)) (brun 3 h))
k2
