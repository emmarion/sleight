; needs: list
; expect: (Succ (Succ (Zero)))
; Predates through Subterm: a function taken out of a list that predates the level.

(def-lvl L0)
(def-fns L0 $ many inc : (many (Nat) n) -> (many (Nat) m) (Succ n))
(let (many fs) (Cons (Fn L0 (many (Nat) n) -> (many (Nat) m)) inc (Nil (Fn L0 (many (Nat) n) -> (many (Nat) m)))))

(def-lvl L1)
(let (erased p) (prove-predates fs L1))

(def-fns L1 $ many apply-head : (many (Nat) x) -> (many (Nat) y)
  (match many fs (((Nat) r))
    (absurd Nil)
    ((Cons a g rest)
      (let (erased q) (prove-subterm g fs))
      (g (predates (predates-subterm p q)) (g (predates (predates-subterm p q)) x)))))

(apply-head (Zero))
