(def-lvl M)
(def-lvl N)
(let ((erased mn)) (prove-predates M N))

(def-adts $ (P : ((TyCtor -> Type) T) -> Type)
  enum
  (many MkP : (erased (TyCtor -> Type) T)
     (erased (Fn N (erased (P T) p) -> (erased (False) f)) g)
     (erased (ValCtor (erased g is w) -> (T)) C)
     (many (Matchable enum T (many C)) m) -> (P T)))

(def-fns M $ (erased p-prop : (erased (TyCtor -> Type) T) (erased (P T) x) (erased (P T) y) -> (erased (Eq (P T) x y) e))
  (let-match erased x (MkP _ g1 C1 m1))
  (let-match erased y (MkP _ g2 C2 m2))
  (open-adt erased m1)
  (open-adt erased m2)
  (Refl _ x))

(def-fns _ $ (many attack : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem)
    (erased (TyCtor -> Type) T) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-fns M $ (erased pp : (erased (P T) x) (erased (P T) y) -> (erased (Eq (P T) x y) e))
    (p-prop T x y))
  (def-fns _ $ (erased omega : (erased (P T) x) -> (erased (False) f))
    (let-match erased x (MkP _ g C m))
    (g x))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (match erased (lem M N mn (P T) (MkIsProp M (P T) pp)) _
      (absurd (Inl _ _ x) (omega x))
      (absurd (Inr _ _ n)
        (def-adts $ (Tn : -> Type) enum (many MkTn : (erased n is w) -> (Tn)))
        (omega (MkP T n MkTn (matchable-of Tn))))))
  (values (level-of absurdity) absurdity))
