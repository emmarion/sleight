; needs: list
; expect: 3
; Calls with no decrease annotation (SUGAR.md 3): where the levels differ the elaborator supplies
; (predates _), where they agree it supplies (subterm _) at the first subterm argument that differs from
; its counterpart; a written (subterm _) still reads the same.

(def-lvl A)
(def-fns A $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(def-lvl B)
(def-fns B $ (many count : (erased Type X) (subterm many (List X) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil a) (Zero))
    ((Cons a hd tl) (inc (count X tl)))))

(def-fns B $ (many count-again : (erased Type X) (subterm many (List X) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil a) (Zero))
    ((Cons a hd tl) (inc (predates _) (count-again X (subterm _) tl)))))

(let ((many xs)) (Cons (Nat) 1 (Cons (Nat) 2 (Cons (Nat) 3 (Nil (Nat))))))
(match many (count (Nat) xs) (((Nat) r))
  ((Zero) (Zero))
  ((Succ k) (count-again (Nat) xs)))
