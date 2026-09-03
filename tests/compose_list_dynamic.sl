; expect: (Succ (Succ (Succ (Succ (Succ (Zero))))))
; Folding a list of functions into one function: each step births a level at runtime above the level the
; recursive call returned, so the composed closure calls the rest under a proof born beside it. The tower
; of levels is as tall as the list and is born when compose-all runs, here in run position;
; runtime_level_bad.sl is the same call from a function body.

(def-lvl M)
(def-fns M $ many inc : (many (Nat) n) -> (many (Nat) m) (Succ n))

(def-lvl C)
(def-fns C $ many compose-all : (subterm many (List (Fn M (many (Nat) x) -> (many (Nat) y))) fs) ->
    (erased (Level) N) (many (Fn N (many (Nat) x) -> (many (Nat) y)) g)
  (match many fs _
    ((Nil a)
      (def-lvl N)
      (def-fns N $ many id : (many (Nat) x) -> (many (Nat) y) x)
      (values N id))
    ((Cons a f rest)
      (let (erased N1) (many g1) (compose-all (subterm (prove-subterm rest fs)) rest))
      (def-lvl N)
      (let (erased p1) (prove-predates N1 N))
      (let (erased pm) (prove-predates M N))
      (def-fns N $ many g : (many (Nat) x) -> (many (Nat) y)
        (f (predates pm) (g1 (predates p1) x)))
      (values N g))))

(let (erased N) (many h) (compose-all (Cons (Fn M (many (Nat) x) -> (many (Nat) y)) inc (Cons (Fn M (many (Nat) x) -> (many (Nat) y)) inc (Nil (Fn M (many (Nat) x) -> (many (Nat) y)))))))
(h 3)
