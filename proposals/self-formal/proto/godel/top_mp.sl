(def-adts $ (Pimp : (Type A) (Type B) -> Type)
  enum
  (many MkPimp : (erased Type A) (erased Type B) (erased (Level) K) (erased (Fn K (erased A a) -> (erased B b)) f) -> (Pimp A B)))
(goal erased (Deriv (Imp (At 2) (Imp (At 0) (Imp (At 1) (At 0))))))
(def-fns _ $ (erased lift : (erased (Deriv (Imp (At 0) (Imp (At 1) (At 0)))) d) ->
    (erased (Deriv (Imp (At 2) (Imp (At 0) (Imp (At 1) (At 0))))) e))
  (MP _ _ (AxK _ (At 2)) d))
(let ((erased h)) (MkPimp _ _ _ lift))
(let-match erased h (MkPimp _ _ K f))
(qed (f (AxK (At 0) (At 1))))
