; error: has no Matchable open
; A Matchable does nothing by being in scope: until it is opened, nothing consults it, and a match on its type
; has nothing to read (DESIGN.md section 19). tests/first_class.sl is this with the open.

(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ (many open : (erased (TyCtor -> Type) T)
    (many (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n))
  (match many x (((Nat) r))
    ((C n) n)))
(open Box MkBox (matchable-of Box) (MkBox (Succ (Zero))))
