; needs: list
; expect: 2

(def-lvl X)

(def-fns X $ (many len-acc : (erased Type A) (subterm many (List A) xs) (many (Nat) acc) -> (many (Nat) n))
  (let-match many xs (Cons a hd tl) ((Nil a) acc))
  (let ((erased p)) (prove-subterm tl xs))
  (tail (len-acc A (subterm p) tl (Succ acc))))

(len-acc (Nat) (Cons (Nat) (Zero) $ Cons (Nat) (Zero) $ Nil (Nat)) (Zero))
