; needs: list map
; expect: (Cons _ 1 $ Cons _ 0 $ Nil _)
; DESIGN.md section 60: unwrapping a list with coerce, and a delegate proof. Needs list.sl and map.sl first.

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

(let ((erased piv)) (prove-predates I V))

(def-fns V $ (many inc-noted : (many (Nat) n) (erased (Nat) note) ->
    (many (Nat) m))
  (delegate (inc (predates piv) n)))

(let ((erased ig)) (coercible-of (delegate-of inc-noted)))

(let ((many ms)) (Cons (Meters) (MkMeters (Succ (Zero))) $ Cons (Meters) (MkMeters (Zero)) $ Nil (Meters)))

(unwrap-all ms)
; warns: tests/coerce.sl:19:53: warning: unnecessary `(subterm _)`; drop it
; warns: tests/coerce.sl:14:4: warning: lopsided `match`; flatten it with a `let-match` on `Cons`
; warns: tests/coerce.sl:34:49: warning: unnecessary `(predates _)`; drop it
; warns: tests/coerce.sl:41:18: warning: unnecessary `(predates _)`; drop it
