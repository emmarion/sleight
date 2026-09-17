; expect: 2
; An open's extent is the rest of the containing expression: a let's right-hand side statements are
; statements of the enclosing expression, their entries staying in scope anonymously (section 16), so the
; open inside the right-hand side still serves the matches after the let, the second of which dispatches at
; runtime through the entry the open bound there.

(def-adts $ Box : -> Type enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n)
  (let (many k) (open-adt many m) (match many x (((Nat) r)) ((C n) n)))
  (let (many j) (match erased x (((Nat) r)) ((C n) (Succ k))))
  (match many x (((Nat) r)) ((C n) (Succ j))))
(open Box MkBox (matchable-of Box) (MkBox (Zero)))
