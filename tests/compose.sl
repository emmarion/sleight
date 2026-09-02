; needs: list
; expect: (Succ (Succ (Succ (Zero))))
; A factory of factories: compose births a level above both argument levels and returns a function there.

(def-lvl F)

(def-fns F $ many compose : (erased (Level) M) (erased (Level) N)
    (many (Fn M (many (Nat) a) -> (many (Nat) b)) g)
    (many (Fn N (many (Nat) a) -> (many (Nat) b)) f) ->
    (erased (Level) L)
    (many (Fn L (many (Nat) x) -> (many (Nat) y)) h)
  (def-lvl L)
  (let (erased pg) (prove-predates M L))
  (let (erased pf) (prove-predates N L))
  (def-fns L $ many h : (many (Nat) x) -> (many (Nat) y)
    (g (predates pg) (f (predates pf) x)))
  (values L h))

(def-fns _ $ many inc : (many (Nat) n) -> (many (Nat) m) (Succ n))
(def-fns _ $ many inc2 : (many (Nat) n) -> (many (Nat) m) (Succ (Succ n)))

(let (erased L) (many inc3) (compose (level-of inc) (level-of inc2) inc inc2))
(let (erased K) (many inc4) (compose L (level-of inc) inc3 inc))

(inc3 (Zero))
