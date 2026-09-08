; error: erased or out of scope
; The entry an open binds inside a let's right-hand side is unbound after it, like the right-hand side's other
; bindings, so a match after the let that would read it at runtime is refused (tests/open_adt_let.sl).

(def-adts $ Box : -> Type enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n)
  (let (many k) (open-adt many m) (match many x (((Nat) r)) ((C n) n)))
  (match many x (((Nat) r)) ((C n) (Succ k))))
(open Box MkBox (matchable-of Box) (MkBox (Zero)))
