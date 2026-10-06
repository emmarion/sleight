; expect: (MkBoth 1 $ PSucc $ PZero)

(def-adts $ (Peano : -> Type)
  enum
  (many PZero : -> (Peano))
  (many PSucc : (many (Peano) pred) -> (Peano)))

(def-adts $ (Both : -> Type)
  enum
  (many MkBoth : (many (Nat) n) (many (Peano) p) -> (Both)))

(def-lvl X)
(def-fns X $ (many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) Z)
    (erased (ValCtor (many (T) p) -> (T)) S)
    (many (Matchable enum T (many Z) (many S)) m)
    (many (T) x) -> (many (T) p))
  (open-adt many m)
  (match many x (((T) r))
    ((Z) x)
    ((S p) p)))

(def-fns X $ (many open-extern : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) Z)
    (erased (ValCtor (many (T) p) -> (T)) S)
    (many (Matchable enum extern T (many Z) (many S)) m)
    (many (T) x) -> (many (T) p))
  (open-adt many m)
  (match many x (((T) r))
    ((Z) x)
    ((S p) p)))

(def-lvl Y)
(let ((erased xy)) (prove-predates X Y))

(def-fns Y $ (many run : -> (many (Both) b))
  (MkBoth (open-extern (predates xy) Nat Zero Succ (matchable-of Nat) (Succ (Succ (Zero))))
          (open (predates xy) Peano PZero PSucc (matchable-of Peano) (PSucc (PSucc (PZero))))))

run
; warns: tests/thunk_matchable.sl:37:24: warning: unnecessary `(predates _)`; drop it
; warns: tests/thunk_matchable.sl:38:17: warning: unnecessary `(predates _)`; drop it
