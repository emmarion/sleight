; needs: list
; error: not in tail position

(def-lvl X)

(def-fns X $ (many len-acc : (erased Type A) (subterm many (List A) xs) (many (Nat) acc) -> (many (Nat) n))
  (let-match many xs (Cons a hd tl)
    ((Nil a) acc))
  (let ((erased p)) (prove-subterm tl xs))
  (Succ (tail (len-acc A (subterm p) tl acc))))
; warns: tests/tail_bad.sl:10:26: warning: unnecessary `(subterm _)`; drop it
