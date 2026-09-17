; needs: list
; expect: 1
; Subterm transitivity, and skipping two elements at a time.

(def-lvl X)
(def-fns X $ many pairs : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n)
  (match many xs (((Nat) r))
    ((Nil a) (Zero))
    ((Cons a hd tl)
      (let (erased p) (prove-subterm tl xs))
      (match many tl (((Nat) r))
        ((Nil b) (Zero))
        ((Cons b hd2 tl2)
          (let (erased q) (prove-subterm tl2 tl))
          (Succ (pairs A (subterm (subterm-trans q p)) tl2)))))))

(pairs (Nat) (Cons (Nat) (Zero) $ Cons (Nat) (Zero) $ Cons (Nat) (Zero) $ Nil (Nat)))
