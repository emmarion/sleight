; externs: only
; expect: 4498500
; extract-bytes-at-most: 200000
; A list built at compile time and folded away: nothing the program runs reaches it, so the OCaml written
; out is not to hold it (BUGS 16).
(def-fns _ $ (many gen-list : (subterm many (Nat) n) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (match many n _ ((Zero) acc) ((Succ j) (tail (gen-list j (Cons (Nat) j acc))))))
(def-fns _ $ (many gen-total : (subterm many (List $ Nat) xs) (many (Nat) acc) -> (many (Nat) r))
  (match many xs _ ((Nil a) acc) ((Cons a x rest) (tail (gen-total rest (nat-add x acc))))))
(let ((many t)) (gen-total (gen-list 3000 (Nil (Nat))) 0))
t
