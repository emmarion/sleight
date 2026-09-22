; needs: list
; expect: 1
; Statements inside a top-level match branch are not in run position but need no proofs (sections 16, 24).
; xs is (Cons ...) is known from its let, so the Nil branch is refuted.

(def-lvl X)
(def-fns X $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(let ((many xs)) (Cons (Nat) (Zero) (Nil (Nat))))

(match many xs (((Nat) r))
  (absurd Nil)
  ((Cons a hd tl)
    (let ((many one)) (inc hd))
    one))
