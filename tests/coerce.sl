; needs: list map
; expect: (Cons (Succ (Zero)) (Cons (Zero) (Nil)))
; DESIGN.md section 40: unwrapping a list with coerce, and a delegate proof. Needs list.sl and map.sl first.

(def-adts $ Meters : -> Type
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl U)

(def-fns U $ erased unwrap-witness : (subterm many (List (Meters)) ms) ->
    (erased (List (Nat)) ns)
    (erased (Coercible (List (Meters)) ms (List (Nat)) ns) p)
  (match erased ms (((List (Nat)) ns)
                    ((Coercible (List (Meters)) ms (List (Nat)) ns) p))
    ((Nil a) (values (Nil (Nat)) (coercible-ctor Nil (Meters) (Nat))))
    ((Cons a m tl)
      (let (erased sp) (prove-subterm tl ms))
      (let (erased ws) (erased q) (unwrap-witness (subterm sp) tl))
      (match erased m (((List (Nat)) ns)
                       ((Coercible (List (Meters)) ms (List (Nat)) ns) p))
        ((MkMeters n)
          (values (Cons (Nat) n ws)
                  (coercible-ctor Cons (Meters) (Nat)
                    (coercible-sym (coercible-wrap MkMeters n))
                    q)))))))

(def-lvl V)

(let (erased puv) (prove-predates U V))

(def-fns V $ many unwrap-all : (many (List (Meters)) ms) ->
    (many (List (Nat)) ns)
  (let (erased ws) (erased p) (unwrap-witness (predates puv) ms))
  (coerce ms p))

(let (erased piv) (prove-predates I V))

(def-fns V $ many inc-noted : (many (Nat) n) (erased (Nat) note) ->
    (many (Nat) m)
  (delegate (inc (predates piv) n)))

(let (erased ig) (coercible-of inc-noted))

(let (many ms) (Cons (Meters) (MkMeters (Succ (Zero))) $ Cons (Meters) (MkMeters (Zero)) $ Nil (Meters)))

(unwrap-all ms)
