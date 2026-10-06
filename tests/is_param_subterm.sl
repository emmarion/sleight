; needs: list
; expect: 1
; A subterm parameter pinned by is: the recursive call decreases through the pinned structure.

(def-lvl X)
(def-fns X $ (many count : (many (Nat) n) (subterm many (Succ n) is m) -> (many (Nat) r))
  (let-match many n (Succ k) ((Zero) m))
  (let ((erased p)) (prove-subterm n m))
  (tail $ count k (subterm p) n))
(count (Succ (Zero)) (Succ (Succ (Zero))))
; warns: tests/is_param_subterm.sl:9:19: warning: unnecessary `(subterm _)`; drop it
