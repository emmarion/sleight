; expect: (MySucc $ MySucc $ MyZero)
; A field written `at` a variable of the enclosing scope: the constructor stores nothing, and the destructure
; binds the field at that variable.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-fns _ $ (many wrap-unwrap : (unique (MyNat) n0) -> (unique (MyNat) r at n0))
  (def-adts $ (W : -> Type) enum (many MkW : (unique (MyNat) n at n0) -> (W)))
  (let ((unique w)) (MkW n0))
  (let-match unique w (MkW n1))
  n1)
(let ((unique two)) (MySucc (MySucc (MyZero))))
(let ((unique r)) (wrap-unwrap two))
(share r)
