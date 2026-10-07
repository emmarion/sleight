; expect: 4
; A match annotation entry written `at` an earlier entry of the annotation (AT_REDESIGN A5): the branch
; returns the one word twice, and the `let` binding the match reconstructs the second from the first (A3).
(def-fns _ $ (many twice : (many (Nat) x) -> (many (Nat) r) (many (Nat) s at r))
  (match many x (((Nat) a) ((Nat) b at a))
    ((Zero) (values x x))
    ((Succ _) (let ((many y)) (Succ x)) (values y y))))
(let ((many p) (many q)) (twice 3))
q
; warns: tests/at_match_sibling.sl:5:4: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
