; needs: list
; error: not in tail position

(def-lvl X)

(def-fns X $ (many len-acc : (erased Type A) (subterm many (List A) xs) (many (Nat) acc) -> (many (Nat) n))
  (match many xs (((Nat) r))
    ((Nil a) acc)
    ((Cons a hd tl)
      (let ((erased p)) (prove-subterm tl xs))
      (Succ (tail (len-acc A (subterm p) tl acc))))))
