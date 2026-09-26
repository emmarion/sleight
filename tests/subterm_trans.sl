; needs: list
; expect: 1
; Subterm transitivity, and skipping two elements at a time.

(def-lvl X)
(def-fns X $ (many pairs : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (let-match many xs (Cons a hd tl) ((Nil a) (Zero)))
  (let ((erased p)) (prove-subterm tl xs))
  (let-match many tl (Cons b hd2 tl2) ((Nil b) (Zero)))
  (let ((erased q)) (prove-subterm tl2 tl))
  (Succ (notail $ pairs A (subterm (subterm-trans q p)) tl2)))

(pairs (Nat) (Cons (Nat) (Zero) $ Cons (Nat) (Zero) $ Cons (Nat) (Zero) $ Nil (Nat)))
