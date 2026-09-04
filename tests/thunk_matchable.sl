; expect: (Succ (Zero))
; A first-class Matchable read when the code runs, over the one type where it is load-bearing: Nat is extern,
; so what takes the scrutinee apart is the FFI's destructor the Matchable carries, not anything in the
; constructors. Being a function from no arguments, this runs in the extracted program too.

(def-lvl X)
(def-fns X $ many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (T) p) -> (T)) S)
    (erased (ValCtor -> (T)) Z)
    (many (Matchable enum T (many Z) (many S)) m)
    (many (T) x) -> (many (T) p)
  (match many x (((T) r))
    ((Z) x)
    ((S p) p)))

(def-lvl Y)
(let (erased xy) (prove-predates X Y))

(def-fns Y $ many run : -> (many (Nat) n)
  (open (predates xy) Nat Succ Zero (matchable-of Nat) (Succ (Succ (Zero)))))

run
