; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify ../mini/core ../mini/eval ../mini/elab ../mini/elabfn ../mini/raw
; expect: (Cons (VCon 5 (Nil)) (Nil))
; Branch refinement and refutation in the minimal language (DESIGN.md sections 12, 18; MINIMAL.md):
;   (def-adts (Box (((Nat) n)) (MkBox (((Nat) m)) (Box m))))
;   (def-fns L (f (((Box (Zero)) b)) (((Nat) r))
;     (match b (((Nat) r)) ((MkBox m) (match m (((Nat) r2)) ((Zero) (Zero)))))))
;   (f (MkBox (Zero)))
; Entering MkBox forces m to be Zero, so the inner match needs no Succ branch, and writing one is refused.

(let (many box-decl)
  (l2 (k (KDefAdts)) (l3 (a "Box") (l1 (l2 nat (a "n"))) (l3 (a "MkBox") (l1 (l2 nat (a "m"))) (l2 (a "Box") (a "m"))))))

(def-fns _ $ many prog : (many (List (Raw)) inner-branches) -> (many (List (Raw)) program)
  (let (many inner) (RList (Cons _ (k (KMatch)) (Cons _ (a "m") (Cons _ (l1 (l2 nat (a "r2"))) inner-branches)))))
  (let (many fns)
    (l3 (k (KDefFns)) (a "L")
      (l4 (a "f") (l1 (l2 (l2 (a "Box") zero) (a "b"))) (l1 (l2 nat (a "r")))
        (l4 (k (KMatch)) (a "b") (l1 (l2 nat (a "r"))) (l2 (l2 (a "MkBox") (a "m")) inner)))))
  (Cons _ nat-decl (Cons _ box-decl (Cons _ lvl-decl (Cons _ fns (Cons _ (l2 (a "f") (l2 (a "MkBox") zero)) (Nil _)))))))

(let (many zero-only) (Cons _ (l2 (l1 (a "Zero")) zero) (Nil _)))
(let (many both) (Cons _ (l2 (l1 (a "Zero")) zero) (Cons _ (l2 (l2 (a "Succ") (a "q")) (a "q")) (Nil _))))
(let (many none) (Nil (Raw)))

(let (many refuted) (outcome (prog both)))
(comptime-match many refuted (Some t r))
(comptime-match many r (RRefutedBranch))
(let (many missing) (outcome (prog none)))
(comptime-match many missing (Some t2 r2))
(comptime-match many r2 (RMissingBranch))

(run (prog zero-only))
