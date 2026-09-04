; expect: ((Succ (Zero)) (PS (PZ)))
; One function matching through nothing but a first-class Matchable, run over two types: Nat, which the FFI
; holds, and a Peano copy declared here, which it does not. Both calls enter the same code, so what tells the
; two apart is only the Matchable each is given -- for Nat the FFI's destructor, for Peano the tag. The
; constructors are passed erased, nothing dispatching on them. Being a function from no arguments, this runs
; in the extracted program too.

(def-adts $ Peano : -> Type
  enum
  (many PZ : -> (Peano))
  (many PS : (many (Peano) pred) -> (Peano)))

(def-adts $ Both : -> Type
  enum
  (many MkBoth : (many (Nat) n) (many (Peano) p) -> (Both)))

(def-lvl X)
(def-fns X $ many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) Z)
    (erased (ValCtor (many (T) p) -> (T)) S)
    (many (Matchable enum T (many Z) (many S)) m)
    (many (T) x) -> (many (T) p)
  (match many x (((T) r))
    ((Z) x)
    ((S p) p)))

(def-lvl Y)
(let (erased xy) (prove-predates X Y))

(def-fns Y $ many run : -> (many (Both) b)
  (MkBoth (open (predates xy) Nat Zero Succ (matchable-of Nat) (Succ (Succ (Zero))))
          (open (predates xy) Peano PZ PS (matchable-of Peano) (PS (PS (PZ))))))

run
