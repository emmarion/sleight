; needs: list
; expect: (Cons _ (Succ (Zero)) (Cons _ (Succ (Succ (Zero))) (Nil _)))
; SUGAR.md section 4: map with _ levels, _ annotations and naive proofs.

(def-fns _ $ many map-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A) (erased Type B)
              (many (Fn M (many A x) -> (many B y)) f)
              (subterm many (List A) xs) ->
              (many (List B) ys))
          mapped)
  (def-fns _ $ many map : (erased Type A) (erased Type B)
      (many (Fn M (many A x) -> (many B y)) f)
      (subterm many (List A) xs) ->
      (many (List B) ys)
    (match many xs _
      ((Nil a) (Nil B))
      ((Cons a hd tl)
        (Cons B (f (predates _) hd) $ map A B f (subterm _) tl))))
  (values (level-of map) map))

(def-fns _ $ many inc : (many (Nat) n) -> (many (Nat) m)
  (Succ n))

(let (erased ML) (many map-nat) (map-factory (level-of inc)))

(let (many xs) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

(map-nat (Nat) (Nat) inc xs)
