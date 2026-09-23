; error: has no `Matchable` open
; An open inside a match branch ends with the branch, as the branch's facts do
; (DESIGN.md section 19): the match after it finds nothing.

(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ (many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m)
    (many (Nat) g)
    (many (T) x) -> (many (Nat) n))
  (let ((many k)) (match many g (((Nat) r)) ((Zero) (open-adt many m) (Zero)) ((Succ j) j)))
  (match many x (((Nat) r)) ((C n) n)))
(open Box MkBox (matchable-of Box) (Zero) (MkBox (Zero)))
