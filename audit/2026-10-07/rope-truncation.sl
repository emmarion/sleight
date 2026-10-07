(def-fns _ $ (many build-rope : (subterm many (Nat) n) (many (Rope) acc) -> (many (Rope) out))
  (match many n _
    ((Zero) acc)
    ((Succ k) (tail (build-rope k (RCat (REmpty) acc))))))
(def-fns _ $ (many compute : -> (many (String) s))
  (let ((many s) (erased proof)) (flatten (build-rope 500000 (RStr "x"))))
  s)
(let ((many s)) (compute))
s
