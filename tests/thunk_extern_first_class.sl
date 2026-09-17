; expect: (2 (PS (PZ)) "aab")
; Extern types reached only through first-class values, in a function from no arguments so the extracted
; program does the work: Nat and String are matched through a held Matchable and rebuilt through a held
; constructor, with nothing at the use site naming the type. The same code runs over a source Peano copy.

(def-adts $ Peano : -> Type
  enum
  (many PZ : -> (Peano))
  (many PS : (many (Peano) pred) -> (Peano)))

(def-adts $ Three : -> Type
  enum
  (many MkThree : (many (Nat) n) (many (Peano) p) (many (String) s) -> (Three)))

(def-lvl X)
(def-fns X $ many bump : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) Z)
    (many (ValCtor (many (T) p) -> (T)) S)
    (many (Matchable enum T (many Z) (many S)) m)
    (many (T) x) -> (many (T) y)
  (open-adt many m)
  (match many x (((T) r))
    ((Z) (S x))
    ((S p) (S (S p)))))

(def-fns X $ many dup-head : (erased (TyCtor -> Type) T) (erased Type C)
    (erased (ValCtor -> (T)) N)
    (many (ValCtor (many C c) (many (T) rest) -> (T)) K)
    (many (Matchable enum T (many N) (many K)) m)
    (many (T) s) -> (many (T) t)
  (open-adt many m)
  (match many s (((T) r))
    ((N) s)
    ((K c rest) (K c (K c rest)))))

(def-lvl Y)
(let (erased xy) (prove-predates X Y))
(def-fns Y $ many run : -> (many (Three) out)
  (MkThree (bump (predates xy) Nat Zero Succ (matchable-of Nat) (Succ (Zero)))
           (bump (predates xy) Peano PZ PS (matchable-of Peano) (PZ))
           (dup-head (predates xy) String (Char) SNil SCons (matchable-of String) "ab")))

run
