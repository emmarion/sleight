; error: return does not satisfy `at`
; Two `is`-equal blocks, forced equal through a `Refl` over inline applications: the field written `at x`
; of a destructure of one is at the destructure's own binder, never at the other block's argument.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (Pair2 : -> Type) enum (many MkPair2 : (many (MyNat) x) (many (MyNat) y at x) -> (Pair2)))
(def-fns _ $ (many f : (many (MyNat) p) (many (MyNat) q) (erased (Eq (Pair2) (MkPair2 p p) (MkPair2 q q)) e) -> (many (MyNat) r at p))
  (let-match erased e (Refl _ _))
  (let ((many pq)) (MkPair2 q q))
  (let-match many pq (MkPair2 x2 y2))
  y2)
(let ((many p)) (MySucc (MyZero)))
(let ((many q)) (MySucc (MyZero)))
(f p q (Refl _ _))
