; error: `l` was not in scope when level `K` was minted
; With neither a bound in the package nor a proof about the list, a packed level has no relation to the
; consumer's, and prove-predates refuses to relate them there.

(def-lvl L1)
(def-fns L1 $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-adts $ (Packed : -> Type)
  enum
  (many Pack : (erased (Level) l) (many (Fn l (many (Nat) x) -> (many (Nat) y)) f) -> (Packed)))
(def-lvl K)
(def-fns K $ (many run-one : (many (Packed) p) (many (Nat) x) -> (many (Nat) y))
  (let-match many p (Pack l f))
  (let ((erased q)) (prove-predates l K))
  (f (predates q) x))
(run-one (Pack L1 inc) 3)
