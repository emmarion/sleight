; mini/raw.sl -- helpers that build the raw syntax of mini/elab.sl by hand, for tests, until a reader from
; text exists; and the environment a program is evaluated in, the built-in entries as values.

(def-fns _ $ (many a : (many (String) s) -> (many (Sexp) r)) (RAtom s))
(def-fns _ $ (many k : (many (Key) x) -> (many (Sexp) r)) (RKey x))
(def-fns _ $ (many l0 : -> (many (Sexp) r)) (RList (Nil _)))
(def-fns _ $ (many l1 : (many (Sexp) x) -> (many (Sexp) r)) (RList (Cons _ x (Nil _))))
(def-fns _ $ (many l2 : (many (Sexp) x) (many (Sexp) y) -> (many (Sexp) r)) (RList (Cons _ x (Cons _ y (Nil _)))))
(def-fns _ $ (many l3 : (many (Sexp) x) (many (Sexp) y) (many (Sexp) z) -> (many (Sexp) r)) (RList (Cons _ x (Cons _ y (Cons _ z (Nil _))))))
(def-fns _ $ (many l4 : (many (Sexp) x) (many (Sexp) y) (many (Sexp) z) (many (Sexp) w) -> (many (Sexp) r)) (RList (Cons _ x (Cons _ y (Cons _ z (Cons _ w (Nil _)))))))
(def-fns _ $ (many l5 : (many (Sexp) x) (many (Sexp) y) (many (Sexp) z) (many (Sexp) w) (many (Sexp) v) -> (many (Sexp) r)) (RList (Cons _ x (Cons _ y (Cons _ z (Cons _ w (Cons _ v (Nil _))))))))

; (def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat)))) and the level L, the start of every test.
(let ((many nat)) (l1 (a "Nat")))
(let ((many zero)) (l1 (a "Zero")))
(let ((many nat-decl)) (l2 (k (KDefAdts)) (l4 (a "Nat") (l0) (l3 (a "Zero") (l0) nat) (l3 (a "Succ") (l1 (l2 nat (a "pred"))) nat))))
(let ((many lvl-decl)) (l2 (k (KDefLvl)) (a "L")))

(let ((many init-env)) (ECons 3 (VFormer (TUniv) (ENil)) (ECons 2 (VAtom 2) (ECons 1 (VAtom 1) (ECons 0 (VAtom 0) (ENil))))))

; Elaborate and run a program, or answer the empty list.
(def-fns _ $ (many run : (many (List (Sexp)) program) -> (many (List (Val)) vs))
  (let-match many (elab-program program) (MkProgramDec _ out _) ((ProgramStuck _) (Nil _)))
  (let-match many out (POk core _) ((PErr _) (Nil _)))
  (match many (eval 500 init-env core) _
    ((EvalStuck _ _) (Nil _))
    ((MkEvaled _ _ vs _) vs)))

; Elaborate a program and report only the outcome's shape.
(def-fns _ $ (many outcome : (many (List (Sexp)) program) -> (many (Maybe (Reason)) r))
  (let-match many (elab-program program) (MkProgramDec _ out _) ((ProgramStuck _) (Some _ (RSize))))
  (match many out _
    ((PErr r) (Some _ r))
    ((POk _ _) (None _))))

(MkUnit)
