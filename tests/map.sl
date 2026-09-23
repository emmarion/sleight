; needs: list
; expect: (Cons _ 1 $ Cons _ 2 $ Nil _)
; DESIGN.md section 33: level-polymorphic map via a factory. Needs list.sl first.

(def-lvl F)

(def-fns F $ (many map-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A) (erased Type B)
              (many (Fn M (many A x) -> (many B y)) f)
              (subterm many (List A) xs) ->
              (many (List B) ys))
          mapped))
  (def-lvl L)
  (let ((erased pml)) (prove-predates M L))
  (def-fns L $ (many map : (erased Type A) (erased Type B)
      (many (Fn M (many A x) -> (many B y)) f)
      (subterm many (List A) xs) ->
      (many (List B) ys))
    (match many xs (((List B) r))
      ((Nil a) (Nil B))
      ((Cons a hd tl)
        (let ((erased p)) (prove-subterm tl xs))
        (Cons B (f (predates pml) hd) $ notail $ map A B f (subterm p) tl))))
  (values L map))

(def-lvl I)

(def-fns I $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))

(let ((erased ML) (many map-nat)) (map-factory I))

(let ((many xs)) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

(map-nat (Nat) (Nat) inc xs)
