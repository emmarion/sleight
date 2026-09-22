; needs: list
; expect: 2
; Predates through Subterm: a function's level is an erased field of a value that predates the caller's level.

(def-adts $ (Packed : -> Type)
  enum
  (many Pack : (erased (Level) l) (many (Fn l (many (Nat) n) -> (many (Nat) m)) f) -> (Packed)))

(def-lvl L0)
(def-fns L0 $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(let ((many p)) (Pack L0 inc))

(def-lvl L1)
(let ((erased pp)) (prove-predates p L1))

(def-fns L1 $ (many apply-packed : (many (Nat) x) -> (many (Nat) y))
  (match many p (((Nat) r))
    ((Pack l f)
      (let ((erased q)) (prove-subterm l p))
      (f (predates (predates-subterm pp q)) (f (predates (predates-subterm pp q)) x)))))

(apply-packed (Zero))
