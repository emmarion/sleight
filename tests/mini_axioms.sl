; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify ../mini/core ../mini/eval ../mini/elab ../mini/elabfn ../mini/raw
; expect: (Cons _ (VToken) $ Nil _)
; The three transitivity axioms of DESIGN.md section 18 in the minimal language:
;   (def-lvl L1) (def-lvl L2) (let (m) (Succ (Zero))) (let (n) (Succ m)) (def-lvl L3)
;   (let (p) (prove-predates L1 L2)) (let (q) (prove-predates L2 L3)) (let (r) (predates-trans p q))
;   (let (s1) (prove-subterm (Zero) m)) (let (s2) (prove-subterm m n)) (let (t) (subterm-trans s1 s2))
;   (let (pn) (prove-predates n L3)) (predates-subterm pn s2)
; whose value is the token every proof is; (predates-trans q p) is refused, its levels not chaining.

(def-fns _ $ (many bind : (many (String) x) (many (Sexp) e) -> (many (Sexp) r)) (l3 (k (KLet)) (l1 (a x)) e))

(def-fns _ $ (many prog : (many (Sexp) final) -> (many (List (Sexp)) program))
  (Cons _ nat-decl $ Cons _ (l2 (k (KDefLvl)) (a "L1")) $ Cons _ (l2 (k (KDefLvl)) (a "L2"))
    $ Cons _ (bind "m" (l2 (a "Succ") zero)) $ Cons _ (bind "n" (l2 (a "Succ") (a "m"))) $ Cons _ (l2 (k (KDefLvl)) (a "L3"))
    $ Cons _ (bind "p" (l3 (k (KProvePredates)) (a "L1") (a "L2"))) $ Cons _ (bind "q" (l3 (k (KProvePredates)) (a "L2") (a "L3")))
    $ Cons _ (bind "r" (l3 (k (KPredatesTrans)) (a "p") (a "q")))
    $ Cons _ (bind "s1" (l3 (k (KProveSubterm)) zero (a "m"))) $ Cons _ (bind "s2" (l3 (k (KProveSubterm)) (a "m") (a "n")))
    $ Cons _ (bind "t" (l3 (k (KSubtermTrans)) (a "s1") (a "s2")))
    $ Cons _ (bind "pn" (l3 (k (KProvePredates)) (a "n") (a "L3")))
    $ Cons _ final $ Nil _))

(let ((many backwards)) (outcome (prog (l3 (k (KPredatesTrans)) (a "q") (a "p")))))
(comptime-match many backwards (Some ty r))
(comptime-match many r (RBadProof))
(let ((many wrong-link)) (outcome (prog (l3 (k (KPredatesSubterm)) (a "pn") (a "s1")))))
(comptime-match many wrong-link (Some ty2 r2))
(comptime-match many r2 (RBadProof))

(run (prog (l3 (k (KPredatesSubterm)) (a "pn") (a "s2"))))
