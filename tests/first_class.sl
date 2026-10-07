; needs: list
; expect: 1
; Matching through a first-class type constructor, constructor and Matchable (section 24), once the Matchable
; is opened (DESIGN.md section 8).

(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

(def-lvl X)

(def-fns X $ (many open : (erased (TyCtor -> Type) T)
    (many (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n))
  (open-adt many m)
  (match many x (((Nat) r))
    ((C n) n)))

(open Box MkBox (matchable-of Box) (MkBox (Succ (Zero))))
