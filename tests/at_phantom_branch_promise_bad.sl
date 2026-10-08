; error: return does not satisfy `at` `(slot-of a)`
; A phantom branch under a non-erased scrutinee keeps the match's `at` promise (sections 14, 36).
(def-adts $ (Ph : -> Type) enum (erased MkPh : -> (Ph)) (many Real : -> (Ph)))
(def-fns _ $ (many g : (many (Nat) a) (many (Nat) b) (many (Ph) s) -> (many (Nat) r at a))
  (match many s (((Nat) r at a))
    ((MkPh) b)
    ((Real) a)))
0
