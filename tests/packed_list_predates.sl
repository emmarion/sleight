; expect: 7
; Functions at different levels in one list, the levels erased and the package naming no bound: the consumer
; takes a proof that the list predates its level, and predates-subterm walks that proof down through each
; Cons and each Pack to the level inside.

(def-lvl L1)
(def-fns L1 $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-lvl L2)
(def-fns L2 $ (many dbl : (many (Nat) n) -> (many (Nat) m)) (nat-add (predates (prove-predates nat-lvl L2)) n n))

(def-adts $ (Packed : -> Type)
  enum
  (many Pack : (erased (Level) l) (many (Fn l (many (Nat) x) -> (many (Nat) y)) f) -> (Packed)))

(let ((many ps)) (Cons (Packed) (Pack L1 inc) (Cons (Packed) (Pack L2 dbl) (Nil (Packed)))))

(def-lvl K)
(let ((erased pk)) (prove-predates ps K))
(def-fns K $ (many run-all : (subterm many (List (Packed)) qs) (erased (Predates (List (Packed)) qs K) pq) (many (Nat) x) -> (many (Nat) y))
  (let-match many qs (Cons _ p rest) ((Nil _) x))
  (let ((erased sr)) (prove-subterm rest qs))
  (let-match many p (Pack l f))
  (let ((erased sl)) (subterm-trans (prove-subterm l p) (prove-subterm p qs)))
  (f (predates (predates-subterm pq sl)) (notail $ run-all (subterm sr) rest (predates-subterm pq sr) x)))

(run-all ps pk 3)
; warns: tests/packed_list_predates.sl:9:70: warning: unnecessary `(predates _)`; drop it
; warns: tests/packed_list_predates.sl:24:60: warning: unnecessary `(subterm _)`; drop it
