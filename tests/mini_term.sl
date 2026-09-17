; needs: ../mini/base ../mini/term
; expect: (Fn (Ref (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))) (Cons ((BFalse) (BFalse) (App (Ref (Succ (Succ (Succ (Zero))))) (Cons (Ref (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))) (Nil)))) (Nil)) (Cons ((BFalse) (BTrue) (App (Bound (Zero)) (Cons (Ref (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))) (Nil)))) (Nil)))
; The term layer of mini/: a binder substituted through a function type, where the return entry sits one
; binder deeper than the level and the parameter; the abstraction back and the assignability decision are
; exercised by the checks below, each expected to come out as noted.

(let (many sub) (Cons _ (Some _ (Ref 7)) (Nil _)))
(let (many t) (Fn (Bound 0) (Cons _ (MkEntry (BFalse) (BFalse) (App (Ref 3) (Cons _ (Bound 0) (Nil _)))) (Nil _)) (Cons _ (MkEntry (BFalse) (BTrue) (App (Bound 0) (Cons _ (Bound 1) (Nil _)))) (Nil _))))

(let (many u) (erased p) (subst sub t))

; Abstracting 7 out of the substituted term gives a term with a binder at its head's argument.
(let (many v) (erased q) (abstract (Cons _ (Some _ 7) (Nil _)) u))
(let (many abstracted)
  (match many v (((Bool) r))
    ((Fn l ps rs) (match many l (((Bool) r)) ((Bound k) (BTrue)) (else (BFalse))))
    (else (BFalse))))
(comptime-match abstracted (BTrue))

; 7 occurs in the substituted term, so it cannot be assigned; 9 may be, its only binder being the return's own.
(let (many no7) (match many (assign-dec 0 7 u) (((Bool) r)) ((ADNo c d e q) (BTrue)) ((ADYes c d e q) (BFalse))))
(comptime-match no7 (BTrue))
(let (many yes9) (match many (assign-dec 0 9 u) (((Bool) r)) ((ADNo c d e q) (BFalse)) ((ADYes c d e q) (BTrue))))
(comptime-match yes9 (BTrue))
u
