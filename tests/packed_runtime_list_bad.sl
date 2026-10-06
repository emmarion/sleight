; error: `ps` was not in scope when level `K` was minted
; The consumer of packed_list_predates.sl handed a list built inside a body after K was minted: prove-predates
; refuses the list-level proof, ps being bound after K. packed_bound.sl is the shape that works there.

(def-lvl L1)
(def-fns L1 $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-adts $ (Packed : -> Type)
  enum
  (many Pack : (erased (Level) l) (many (Fn l (many (Nat) x) -> (many (Nat) y)) f) -> (Packed)))
(def-lvl K)
(def-fns K $ (many run-all : (subterm many (List (Packed)) qs) (erased (Predates (List (Packed)) qs K) pq) (many (Nat) x) -> (many (Nat) y))
  (let-match many qs (Cons a p rest)
    ((Nil a) x))
  (let ((erased sr)) (prove-subterm rest qs))
  (let-match many p (Pack l f))
  (let ((erased sl)) (subterm-trans (prove-subterm l p) (prove-subterm p qs)))
  (f (predates (predates-subterm pq sl)) (notail $ run-all (subterm sr) rest (predates-subterm pq sr) x)))
(def-lvl Z)
(let ((erased kz)) (prove-predates K Z))
(def-fns Z $ (many main : (many (Nat) n) -> (many (Nat) r))
  (let ((many ps)) (Cons (Packed) (Pack L1 inc) (Nil (Packed))))
  (let ((erased pk)) (prove-predates ps K))
  (run-all (predates kz) ps pk n))
(main 3)
; warns: tests/packed_runtime_list_bad.sl:17:60: warning: unnecessary `(subterm _)`; drop it
