; expect: _
(let ((unique a) (erased all)) (array-new (Slot) (Succ (Zero))))
(let ((many s)) (slot-of a))
(def-fns _ $ (many cyclic : -> (many (Slot) r)) s)
(let-match erased all (AUCons _ _ _ q))
(let-match erased q (AUNil _))
(let ((unique b) (erased placed))
  (array-place _ _ a (Zero) (Init _ (slot-of cyclic)) _ (NthZ _ _ _ _)))
(let-match erased placed (SetZ _ _ _ _ _))
(let ((erased raw) (erased witness))
  (init-witness _ _ b (AICons _ _ _ _ (AINil _))))
(let ((unique initialized)) (coerce b witness))
(let ((many result)) (share initialized))
cyclic
