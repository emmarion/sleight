; needs: list
; expect: 3
; Calls with no decrease annotation (DESIGN.md section 48): where the levels differ the elaborator supplies
; (predates _), where they agree it supplies (subterm _) at the first subterm argument that differs from
; its counterpart; a written (subterm _) still reads the same.

(def-lvl A)
(def-fns A $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(def-lvl B)
(def-fns B $ (many count : (erased Type X) (subterm many (List X) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil _) (Zero))
    ((Cons _ _ tl) (inc (notail $ count X tl)))))

(def-fns B $ (many count-again : (erased Type X) (subterm many (List X) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil _) (Zero))
    ((Cons _ _ tl) (inc (predates _) (notail $ count-again X (subterm _) tl)))))

(let ((many xs)) (Cons (Nat) 1 (Cons (Nat) 2 (Cons (Nat) 3 (Nil (Nat))))))
(match many (count (Nat) xs) (((Nat) r))
  ((Zero) (Zero))
  ((Succ _) (count-again (Nat) xs)))
; warns: tests/bare_call.sl:19:62: warning: unnecessary `(subterm _)`; drop it
; warns: tests/bare_call.sl:19:25: warning: unnecessary `(predates _)`; drop it
