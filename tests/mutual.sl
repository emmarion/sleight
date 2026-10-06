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
  (let-match many a (Succ k) ((Zero) b))
  (let ((erased p)) (prove-subterm k a))
  (Succ (notail $ plus (subterm p) k b)))

(def-lvl X)
(let ((erased pa)) (prove-predates W X))

(def-fns X
  ((many size : (subterm many (Tree) t) -> (many (Nat) n))
    (let-match many t (Node kids))
    (let ((erased p)) (prove-subterm kids t))
    (Succ (notail $ fsize (subterm p) kids)))
  ((many fsize : (subterm many (Forest) f) -> (many (Nat) n))
    (let-match many f (FCons t rest) ((FNil) (Zero)))
    (let ((erased p)) (prove-subterm t f))
    (let ((erased q)) (prove-subterm rest f))
    (plus (predates pa) (notail $ size (subterm p) t) (notail $ fsize (subterm q) rest))))

(size (Node (FCons (Node (FNil)) (FNil))))
; warns: tests/mutual.sl:19:24: warning: unnecessary `(subterm _)`; drop it
; warns: tests/mutual.sl:28:27: warning: unnecessary `(subterm _)`; drop it
; warns: tests/mutual.sl:33:40: warning: unnecessary `(subterm _)`; drop it
; warns: tests/mutual.sl:33:71: warning: unnecessary `(subterm _)`; drop it
; warns: tests/mutual.sl:33:11: warning: unnecessary `(predates _)`; drop it
