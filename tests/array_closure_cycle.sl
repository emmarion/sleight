; expect: _
(let ((erased xs) (unique a) (erased all)) (array-new (Slot) (Succ (Zero))))
(let ((many s)) (slot-of a))
(def-fns _ $ (many cyclic : -> (many (Slot) r)) s)
(let-match erased all (RepeatCons _ _ _ _ q))
(let-match erased q (RepeatNil _ _))
(let ((erased ys) (unique b) (erased placed))
  (array-place _ _ a (Zero) (Init _ (slot-of cyclic)) _ (NthHere _ _ _)))
(let-match erased placed (SetHere _ _ _ _))
(let ((erased raw) (erased witness))
  (init-witness _ _ _ b (AICons _ _ _ _ (AINil _))))
(let ((unique initialized)) (coerce b witness))
(let ((many result)) (share initialized))
cyclic
