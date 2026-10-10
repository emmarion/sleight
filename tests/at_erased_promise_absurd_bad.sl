; error: return does not satisfy `at` `(slot-of x)`
; Unchecked, the erased promise would let `use` read a `(B (MkUnit))` word as a `Choice` and run
; `explode` on a `(False)` (section 14).
(def-adts $ (Choice : -> Type) enum
  (many HasUnit : (many (Unit) u) -> (Choice))
  (many HasFalse : (many (False) f) -> (Choice)))
(def-adts $ (Two : -> Type) enum
  (many A : (many (Unit) u) -> (Two))
  (many B : (many (Unit) u) -> (Two)))
(def-fns _ $ (erased lie : (erased Type T) (erased Type S) (many T x) (many S y) ->
    (erased S r at x) (erased (Eq (Slot) (slot-of r) (slot-of y)) p))
  (values y (Refl _ (slot-of y))))
(def-fns _ $ (many absurd explode : (many (False) f) -> (many (Nat) n)) f)
(def-fns _ $ (many use : (many (Two) x) (many (Choice) y at x) -> (many (Nat) r))
  (match many y _
    ((HasUnit u) 0)
    ((HasFalse f) (explode f))))
(def-fns _ $ (many go : (many (Two) a) (many (Choice) b) -> (many (Nat) r))
  (let ((erased r) (erased p)) (lie (Two) (Choice) a b))
  (let-match erased p (Refl _ _))
  (use a b))
(go (B (MkUnit)) (HasUnit (MkUnit)))
