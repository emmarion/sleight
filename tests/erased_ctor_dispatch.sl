; expect: 1
; A match reads its Matchable, not its constructors: the branches' discriminants are stamped in at
; elaboration from the Matchable's type, so first-class constructors may be passed erased. Only the
; Matchable itself must be non-erased, since it is what says how an extern type is taken apart.

(def-adts $ Box : -> Type
  enum
  (many MkBox : (many (Nat) n) -> (Box))
  (many Empty : -> (Box)))

(def-lvl X)
(def-fns X $ many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (ValCtor -> (T)) D)
    (many (Matchable enum T (many C) (many D)) m)
    (many (T) x) -> (many (Nat) n)
  (open-adt many m)
  (match many x (((Nat) r))
    ((C n) n)
    ((D) (Zero))))

(open Box MkBox Empty (matchable-of Box) (MkBox (Succ (Zero))))
