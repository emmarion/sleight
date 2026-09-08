; expect: (Zero)
; An erased Matchable still serves a match that compiles to no dispatch: an erased scrutinee has one real
; branch, and an erased position leaves no code at all.

(def-adts $ Box : -> Type
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

(def-lvl X)
(def-fns X $ many peek : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Matchable enum T (many C)) m)
    (erased (T) x) -> (many (Nat) n)
  (open-adt m)
  (match erased x (((Nat) r))
    ((C n) (Zero))))

(peek Box MkBox (matchable-of Box) (MkBox (Succ (Zero))))
