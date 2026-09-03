; expect: (Succ (Succ (Zero)))
; A nested def-fns closes over binders that the enclosing body's lets only rename, which
; ASSUMPTIONS 72's normalization resolves away: the renaming has to reach the nested body too.

(def-lvl L)
(def-lvl M)
(let (erased pm) (prove-predates L M))

(def-fns M $ many outer : (many (Nat) n) -> (many (Nat) r)
  (let (many k) n)
  (let (many _) (many b) (values k k))
  (def-fns L $ many inner : (many (Nat) x) -> (many (Nat) y)
    (Succ b))
  (inner (predates pm) n))

(outer (Succ (Zero)))
