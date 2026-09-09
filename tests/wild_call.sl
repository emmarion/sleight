; needs: list
; expect: (Succ (Succ (Zero)))
; `_` for a call's erased type argument, solved from a later argument and, for a multi-return callee, from
; the telescope its results are returned into.

(def-lvl A)
(def-fns A $ many length : (erased Type X) (subterm many (List X) xs) -> (many (Nat) n)
  (match many xs _
    ((Nil a) (Zero))
    ((Cons a hd tl) (Succ (length _ tl)))))

(def-fns A $ many split : (erased Type X) (many (List X) xs) -> (many (List X) l) (many (List X) r)
  (values xs (Nil _)))

(def-lvl B)
(def-fns B $ many both : (many (List (Nat)) xs) -> (many (List (Nat)) l) (many (List (Nat)) r)
  (split _ xs))

(def-fns B $ many count : (many (List (Nat)) xs) -> (many (Nat) n)
  (tail (length _ xs)))

(let (many l) (many r) (both (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat))))))
(count l)
