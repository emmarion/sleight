(def-adts $ (Dec : ((Nat) a) ((Nat) b) -> Type)
  enum
  (many MkDec : (erased (Nat) n) -> (Dec (Succ n) n)))
(def-fns _
  ((many dec-step : (many (Nat) n) -> (many (Nat) m) (erased (Dec (Succ n) m) p)) (values n (MkDec n)))
  ((erased dec-det : (erased (Nat) n) (erased (Nat) a) (erased (Nat) b) (erased (Dec n a) p) (erased (Dec n b) q) -> (erased (Eq (Nat) a b) e))
    (let-match erased p (MkDec x))
    (let-match erased q (MkDec y))
    (Refl _ a)))
(def-fns _ $ (erased halts-all : (subterm erased (Nat) s) -> (erased (Halts Dec s) h))
  (match erased s _
    ((Zero) (HDone Dec))
    ((Succ n) (HStep Dec n n (MkDec n) (halts-all n)))))
(let ((erased L2) (many brun)) (run-factory (level-of dec-step) Dec dec-step dec-det))
(def-fns _ $ (many run-any : (many (Nat) s) -> (many (Nat) k))
  (let ((erased h)) (halts-all s))
  (let ((many k) (erased r)) (brun s h))
  k)
(run-any 7)
