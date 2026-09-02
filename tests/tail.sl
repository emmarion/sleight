; needs: list
; expect: (Succ (Succ (Zero)))

(def-lvl X)

(def-fns X $ many len-acc : (erased Type A) (subterm many (List A) xs) (many (Nat) acc) -> (many (Nat) n)
  (match many xs (((Nat) r))
    ((Nil a) acc)
    ((Cons a hd tl)
      (let (erased p) (prove-subterm tl xs))
      (tail (len-acc A (subterm p) tl (Succ acc))))))

(len-acc (Nat) (Cons (Nat) (Zero) $ Cons (Nat) (Zero) $ Nil (Nat)) (Zero))
