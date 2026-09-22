; needs: list
; expect: 2
; Mutually recursive ADTs and functions.

(def-adts
  ((Tree : -> Type)
    enum
    (many Node : (many (Forest) kids) -> (Tree)))
  ((Forest : -> Type)
    enum
    (many FNil : -> (Forest))
    (many FCons : (many (Tree) t) (many (Forest) rest) -> (Forest))))

(def-lvl W)

(def-fns W $ (many plus : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) n))
  (match many a (((Nat) r))
    ((Zero) b)
    ((Succ k)
      (let ((erased p)) (prove-subterm k a))
      (Succ (plus (subterm p) k b)))))

(def-lvl X)
(let ((erased pa)) (prove-predates W X))

(def-fns X
  ((many size : (subterm many (Tree) t) -> (many (Nat) n))
    (match many t (((Nat) r))
      ((Node kids)
        (let ((erased p)) (prove-subterm kids t))
        (Succ (fsize (subterm p) kids)))))
  ((many fsize : (subterm many (Forest) f) -> (many (Nat) n))
    (match many f (((Nat) r))
      ((FNil) (Zero))
      ((FCons t rest)
        (let ((erased p)) (prove-subterm t f))
        (let ((erased q)) (prove-subterm rest f))
        (plus (predates pa) (size (subterm p) t) (fsize (subterm q) rest))))))

(size (Node (FCons (Node (FNil)) (FNil))))
