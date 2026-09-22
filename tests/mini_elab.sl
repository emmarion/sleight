; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify ../mini/core ../mini/eval ../mini/elab ../mini/elabfn ../mini/raw
; expect: (Cons _ (VCon 6 $ Cons _ (VCon 5 $ Nil _) $ Nil _) $ Nil _)
; The minimal language end to end: a program declaring Nat, a level, a predecessor function matching on its
; argument, and a call, built as raw syntax, elaborated by mini/elabfn.sl to core code, and evaluated by
; mini/eval.sl. The program is
;   (def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
;   (def-lvl L)
;   (def-fns L (pred (((Nat) n)) (((Nat) r)) (match n (((Nat) r)) ((Zero) (Zero)) ((Succ k) k))))
;   (pred (Succ (Succ (Zero))))
; and its value is one, Succ applied to Zero, the two constructors being entries 6 and 5.

(let ((many body)) (l5 (k (KMatch)) (a "n") (l1 (l2 nat (a "r"))) (l2 (l1 (a "Zero")) zero) (l2 (l2 (a "Succ") (a "k")) (a "k"))))
(let ((many fns)) (l3 (k (KDefFns)) (a "L") (l4 (a "pred") (l1 (l2 nat (a "n"))) (l1 (l2 nat (a "r"))) body)))
(let ((many call)) (l2 (a "pred") (l2 (a "Succ") (l2 (a "Succ") zero))))
(run (Cons _ nat-decl (Cons _ lvl-decl (Cons _ fns (Cons _ call (Nil _))))))
