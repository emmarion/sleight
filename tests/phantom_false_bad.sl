; needs: absurd
; error: constructor `G` has 0 branches
; A phantom constructor's branch under a many scrutinee can never run, but it still owes its (erased) result: were
; the branch allowed to be omitted, boo would be a proof of Ghost -> False, (G) inhabits Ghost in erased positions,
; and the by-proof refutation of a reachable Succ branch below would be accepted and reached at runtime.

(def-adts $ (Ghost : -> Type)
  enum
  (erased G : -> (Ghost)))

(def-lvl X)

(def-fns X $ (many boo : (many (Ghost) g) -> (many (False) x))
  (match many g (((False) x))))

(def-lvl Y)
(let ((erased pxy)) (prove-predates X Y))

(def-fns Y $ (many pred : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) (Zero))
    (absurd (Succ k) (boo (predates pxy) (G)))))

(pred (Succ (Zero)))
