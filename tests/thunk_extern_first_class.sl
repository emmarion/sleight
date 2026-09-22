; expect: (MkThree 2 (PSucc $ PZero) "aab")

(def-adts $ (Peano : -> Type)
  enum
  (many PZero : -> (Peano))
  (many PSucc : (many (Peano) pred) -> (Peano)))

(def-adts $ (Three : -> Type)
  enum
  (many MkThree : (many (Nat) n) (many (Peano) p) (many (String) s) -> (Three)))

(def-lvl X)
(def-fns X $ (many bump : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) Z)
    (many (ValCtor (many (T) p) -> (T)) S)
    (many (Matchable enum T (many Z) (many S)) m)
    (many (T) x) -> (many (T) y))
  (open-adt many m)
  (match many x (((T) r))
    ((Z) (S x))
    ((S p) (S (S p)))))

(def-fns X $ (many bump-extern : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) Z)
    (many (ValCtor (many (T) p) -> (T)) S)
    (many (Matchable enum extern T (many Z) (many S)) m)
    (many (T) x) -> (many (T) y))
  (open-adt many m)
  (match many x (((T) r))
    ((Z) (S x))
    ((S p) (S (S p)))))

(def-fns X $ (many dup-head : (erased (TyCtor -> Type) T) (erased Type C)
    (erased (ValCtor -> (T)) N)
    (many (ValCtor (many C c) (many (T) rest) -> (T)) K)
    (many (Matchable enum extern T (many N) (many K)) m)
    (many (T) s) -> (many (T) t))
  (open-adt many m)
  (match many s (((T) r))
    ((N) s)
    ((K c rest) (K c (K c rest)))))

(def-lvl Y)
(let ((erased xy)) (prove-predates X Y))
(def-fns Y $ (many run : -> (many (Three) out))
  (MkThree (bump-extern (predates xy) Nat Zero Succ (matchable-of Nat) (Succ (Zero)))
           (bump (predates xy) Peano PZero PSucc (matchable-of Peano) (PZero))
           (dup-head (predates xy) String (Char) SNil SCons (matchable-of String) "ab")))

run
