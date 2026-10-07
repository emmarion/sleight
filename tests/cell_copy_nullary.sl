; expect: (A)
; A `many` cell of a nullary constructor, copied by `cell-write`, in a tagged enum and in a union.
(def-adts $ (D : -> Type)
  enum
  (many A : -> (D))
  (many B : (many (Nat) n) -> (D)))
(def-adts $ (E : -> Type)
  union
  (many One : -> (E)))
(def-fns _ $ (many copy : (many (D) x) -> (unique (D) r))
  (match many x _
    ((A u) (let ((unique u2)) (cell-write many u (A))) (u2))
    ((B n u) (let ((unique u2)) (cell-write many u (B _))) (u2 n))))
(def-fns _ $ (many copy-one : (many (E) x) -> (unique (E) r))
  (let-match many x (One u))
  (let ((unique u2)) (cell-write many u (One)))
  (u2))
(let ((unique e)) (copy-one (One)))
(let ((unique r)) (copy (A)))
(share r)
