; needs: list
; expect: (Cons 1 (Nil))
; A match annotation may hold `_`s; they are solved against the expected telescope before any branch, and
; so may a let binder's type, solved by the right-hand side.

(def-lvl L)
(def-fns L $ many f : (many (Nat) n) -> (many (List (Nat)) xs) (many (Maybe (Nat)) m)
  (let (many (List _) ys) (Cons _ n (Nil _)))
  (match many n (((List _) r) ((Maybe _) m))
    ((Zero) (values ys (None _)))
    ((Succ k) (values ys (Some _ k)))))

(let (many xs) (many m) (f (Succ (Zero))))
xs
