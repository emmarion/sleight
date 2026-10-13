(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl U)

(def-fns U $ (erased unwrap-witness : (subterm many (List (Meters)) ms) ->
    (erased (List (Nat)) ns)
    (erased (Coercible (Shared) (List (Meters)) ms (Shared) (List (Nat)) ns) p))
  (match erased ms (((List (Nat)) ns)
                    ((Coercible (Shared) (List (Meters)) ms (Shared) (List (Nat)) ns) p))
    ((Nil a) (values (Nil (Nat)) (coercible-ctor (Shared) Nil (Meters) (Nat))))
    ((Cons a m tl)
      (let ((erased sp)) (prove-subterm tl ms))
      (let ((erased ws) (erased q)) (unwrap-witness (subterm sp) tl))
      (match erased m (((List (Nat)) ns)
                       ((Coercible (Shared) (List (Meters)) ms (Shared) (List (Nat)) ns) p))
        ((MkMeters n)
          (values (Cons (Nat) n ws)
                  (coercible-ctor (Shared) Cons (Meters) (Nat)
                    (coercible-sym (coercible-wrap (Shared) MkMeters n))
                    q)))))))

(def-lvl V)

(let ((erased puv)) (prove-predates U V))

(def-fns V $ (many unwrap-all : (many (List (Meters)) ms) ->
    (many (List (Nat)) ns))
  (let ((erased ws) (erased p)) (unwrap-witness (predates puv) ms))
  (coerce ms p))

(let ((many ms)) (Cons (Meters) (MkMeters 1) $ Cons (Meters) (MkMeters 0) $ Nil (Meters)))

(unwrap-all ms)
