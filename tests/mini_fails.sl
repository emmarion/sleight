; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify ../mini/core ../mini/eval ../mini/elab ../mini/elabfn ../mini/raw
; expect: (Cons (Some (RMissingBranch)) (Cons (Some (RMismatch)) (Cons (Some (RUnbound)) (Cons (Some (RArity)) (Cons (Some (RTopLevelOnly)) (Cons (None) (Nil)))))))
; Programs the minimal language refuses, each with the reason its Fails derivation carries: a match missing
; its Succ branch; Succ applied to a type; an unbound name; Succ applied to two arguments; a def-adts
; inside a function body. The last program, Succ applied to Zero, is accepted.

(def-fns _ $ many with-fn : (many (List (Raw)) body) -> (many (List (Raw)) program)
  (Cons _ nat-decl (Cons _ lvl-decl (Cons _ (l3 (k (KDefFns)) (a "L") (RList (Cons _ (a "f") (Cons _ (l1 (l2 nat (a "n"))) (Cons _ (l1 (l2 nat (a "r"))) body))))) (Cons _ (l2 (a "f") zero) (Nil _))))))

(let (many missing) (outcome (with-fn (Cons _ (l4 (k (KMatch)) (a "n") (l1 (l2 nat (a "r"))) (l2 (l1 (a "Zero")) zero)) (Nil _)))))
(let (many mismatch) (outcome (Cons _ nat-decl (Cons _ (l2 (a "Succ") nat) (Nil _)))))
(let (many unbound) (outcome (Cons _ nat-decl (Cons _ (l1 (a "foo")) (Nil _)))))
(let (many arity) (outcome (Cons _ nat-decl (Cons _ (l3 (a "Succ") zero zero) (Nil _)))))
(let (many nested) (outcome (with-fn (Cons _ (l2 (k (KDefAdts)) (l2 (a "Unit") (l0))) (Cons _ (a "n") (Nil _))))))
(let (many fine) (outcome (Cons _ nat-decl (Cons _ (l2 (a "Succ") zero) (Nil _)))))
(Cons _ missing (Cons _ mismatch (Cons _ unbound (Cons _ arity (Cons _ nested (Cons _ fine (Nil _)))))))
