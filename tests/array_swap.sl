; expect: 12
(def-fns _ $ many swap-second : (unique (Array (Nat) (Succ (Succ (Succ (Zero))))) a)
    (erased (ANth (Nat) (Succ (Succ (Succ (Zero)))) a (Succ (Zero)) (Succ (Succ (Zero)))) nth) ->
    (unique (Succ (Succ (Zero))) is old)
    (unique (Array (Nat) (Succ (Succ (Succ (Zero))))) r at a)
  (let (unique old) (unique r) (erased p)
    (array-swap _ _ a (Succ (Zero)) (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) _ nth))
  (values old r))
(def-fns _ $ many swap-test : -> (many (Nat) result)
  (let (unique a) (ACons _ _ (Succ (Zero))
    (ACons _ _ (Succ (Succ (Zero)))
      (ACons _ _ (Succ (Succ (Succ (Zero)))) (ANil (Nat))))))
  (let (unique old) (unique b) (swap-second a (NthS _ _ _ _ _ _ (NthZ _ _ _ _))))
  (let-match unique b (ACons _ _ x tl))
  (let-match unique tl (ACons _ _ y tail))
  (let-match unique tail (ACons _ _ z end))
  (nat-add (share old) (nat-add (share x) (nat-add (share y) (share z)))))
swap-test
