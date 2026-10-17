; needs: list
; expect: (Cons _ 1 $ Cons _ 0 $ Nil _)
; An else through a first-class Matchable dispatches on the constructor's position, naming no constructor.

(def-adts $ (Two : -> Type)
  enum
  (many L : (many (Nat) n) -> (Two))
  (many R : (many (Nat) n) -> (Two)))

(def-lvl X)

(def-fns X $ (many pick : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (ValCtor (many (Nat) n) -> (T)) D)
    (many (Matchable enum T (many C) (many D)) m)
    (many (T) x) -> (many (Nat) n))
  (open-adt many m)
  (match many x (((Nat) r))
    ((C n) n)
    (else (Zero))))

(Cons (Nat) (pick Two L R (matchable-of Two) (L (Succ (Zero)))) $ Cons (Nat) (pick Two L R (matchable-of Two) (R (Succ (Zero)))) $ Nil (Nat))
