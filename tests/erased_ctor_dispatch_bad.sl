; error: cannot dispatch on it
; A non-erased match dispatches on its constructors at runtime, so a first-class constructor it names must be
; non-erased too: an erased constructor variable has no runtime value to compare the discriminant against.

(def-adts $ Box : -> Type
  enum
  (many MkBox : (many (Nat) n) -> (Box))
  (many Empty : -> (Box)))

(def-lvl X)
(def-fns X $ many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m)
    (many (T) x) -> (many (Nat) n)
  (match many x (((Nat) r))
    ((C n) n)
    ((D) (Zero))))

(open Box MkBox Empty (matchable-of Box) (MkBox (Succ (Zero))))
