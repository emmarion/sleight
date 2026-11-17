(def-adts $ (Dec : ((Nat) a) ((Nat) b) -> Type)
  enum
  (many MkDec : (erased (Nat) n) -> (Dec (Succ n) n)))
(def-fns _
  ((many dec-step : (many (Nat) n) -> (many (Nat) m) (erased (Dec (Succ n) m) p)) (values n (MkDec n)))
  ((erased dec-det : (erased (Nat) n) (erased (Nat) a) (erased (Nat) b) (erased (Dec n a) p) (erased (Dec n b) q) -> (erased (Eq (Nat) a b) e))
    (let-match erased p (MkDec x))
    (let-match erased q (MkDec y))
    (Refl _ a)))
(let ((erased L) (many run)) (run-factory (level-of dec-step) Dec dec-step dec-det))
(let ((erased h)) (HStep Dec (Succ (Zero)) (Succ (Zero)) (MkDec (Succ (Zero))) $ HStep Dec (Zero) (Zero) (MkDec (Zero)) $ HDone Dec))
(let ((many k) (erased r)) (run (Succ (Succ (Zero))) h))
k
