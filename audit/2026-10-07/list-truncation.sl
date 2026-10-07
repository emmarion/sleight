(def-fns _ $ (many build-list : (subterm many (Nat) n) (many (List (Copy (Nat))) acc) -> (many (List (Copy (Nat))) out))
  (match many n _
    ((Zero) acc)
    ((Succ k) (tail (build-list k (Cons _ (MkCopy _ 7) acc))))))
(def-fns _ $ (many compute : -> (many (Nat) n))
  (let ((unique a)) (list-to-array _ (build-list 1000001 (Nil _))))
  (let ((many n) (erased proof) (unique a2)) (array-length _ _ a))
  n)
(let ((many n)) (compute))
n
