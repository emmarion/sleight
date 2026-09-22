; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify ../mini/core ../mini/eval ../mini/elab ../mini/elabfn ../mini/raw
; expect: (Cons _ (VCon 6 $ Cons _ (VCon 6 $ Cons _ (VCon 6 $ Cons _ (VCon 6 $ Cons _ (VCon 5 $ Nil _) $ Nil _) $ Nil _) $ Nil _) $ Nil _) $ Nil _)
; A same-level recursive call in the minimal language, with its Subterm proof (DESIGN.md sections 8, 9):
;   (def-fns L (double ((subterm (Nat) n)) (((Nat) r))
;     (match n (((Nat) r))
;       ((Zero) (Zero))
;       ((Succ k) (let (p) (prove-subterm k n)) (Succ (Succ (double (subterm p) k)))))))
;   (double (Succ (Succ (Zero))))
; evaluates to four; the same call with no annotation is refused for want of a proof, and with the
; parameter unmarked the annotation is refused.

; the branch's body: the let of the proof, then the doubled call
(def-fns _ $ (many double-prog : (many (Raw) param) (many (List (Raw)) call) -> (many (List (Raw)) program))
  (let ((many branch))
    (l3 (l2 (a "Succ") (a "k"))
      (l3 (k (KLet)) (l1 (a "p")) (l3 (k (KProveSubterm)) (a "k") (a "n")))
      (l2 (a "Succ") (l2 (a "Succ") (RList (Cons _ (a "double") call))))))
  (let ((many fns))
    (l3 (k (KDefFns)) (a "L")
      (l4 (a "double") (l1 param) (l1 (l2 nat (a "r")))
        (l5 (k (KMatch)) (a "n") (l1 (l2 nat (a "r"))) (l2 (l1 (a "Zero")) zero) branch))))
  (Cons _ nat-decl (Cons _ lvl-decl (Cons _ fns (Cons _ (l2 (a "double") (l2 (a "Succ") (l2 (a "Succ") zero))) (Nil _))))))

(let ((many marked)) (l3 (k (KSubterm)) nat (a "n")))
(let ((many unmarked)) (l2 nat (a "n")))
(let ((many with-proof)) (Cons _ (l2 (k (KSubterm)) (a "p")) (Cons _ (a "k") (Nil _))))
(let ((many bare)) (Cons _ (a "k") (Nil _)))

(let ((many no-proof)) (outcome (double-prog marked bare)))
(comptime-match many no-proof (Some t r))
(comptime-match many r (RNoProof))
(let ((many not-marked)) (outcome (double-prog unmarked with-proof)))
(comptime-match many not-marked (Some t2 r2))
(comptime-match many r2 (RBadProof))

(run (double-prog marked with-proof))
