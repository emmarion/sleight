; expect: 7
; A union newtype with several wrapping constructors (section 38): each wraps its own field type at no
; cost, the index telling them apart, and NoEither is fieldless. Rewrapping 7 from Left to Right goes
; through the field.

(def-adts
  ((Either : (Type A) (Type B) ((Bool) k) -> Type)
    union newtype
    (many Left : (erased Type A) (erased Type B) (many A x) -> (Either A B (BTrue)))
    (many Right : (erased Type A) (erased Type B) (many B y) -> (Either A B (BFalse)))
    (many NoEither : (erased Type A) (erased Type B) (erased (False) f) -> (Either A B (BFalse)))))

(def-fns _ $ (many get-left : (erased Type A) (erased Type B) (many (Either A B (BTrue)) e) -> (many A a))
  (match many e _
    ((Left _ _ x) x)
    (absurd Right)
    (absurd NoEither)))

(def-fns _ $ (many get-right : (erased Type A) (erased Type B) (many (Either A B (BFalse)) e) -> (many B b))
  (match many e _
    (absurd Left)
    ((Right _ _ y) y)
    (absurd (NoEither _ _ f) f)))

(let ((many n)) 7)
(let ((many t)) (BTrue))
(let ((many r)) (coerce t (coercible-wrap (Shared) Right (Nat) (Bool) t)))
(let ((many b)) (get-right _ _ r))
(comptime-match many b (BTrue))
(let ((many l)) (coerce n (coercible-wrap (Shared) Left (Nat) (Nat) n)))
(let ((many l2)) (coerce l (coercible-trans (coercible-sym (coercible-wrap (Shared) Left (Nat) (Nat) n))
                                           (coercible-wrap (Shared) Right (Nat) (Nat) n))))
(get-right _ _ l2)
