; expect: 2
; open-adt is an anonymous let at the written multiplicity followed by the open, so its argument may be any
; expression (DESIGN.md section 19, ASSUMPTIONS 139): here a call's result, opened at many
; inside a body, where the match reads the bound value at runtime, and at top level, where the call runs at
; once and the entry is Const, merging with Box's own.

(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ (many same : (erased (TyCtor -> Type) T) (erased (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m) -> (many (Matchable enum T (many C)) r))
  m)
(def-lvl Y)
(def-fns Y $ (many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n))
  (open-adt many (same T C m))
  (match many x (((Nat) r)) ((C n) n)))
(open-adt many (same Box MkBox (matchable-of Box)))
(def-fns Y $ (many peek : (many (Box) b) -> (many (Nat) n))
  (match many b (((Nat) r)) ((MkBox n) (Succ n))))
(peek (MkBox (open Box MkBox (matchable-of Box) (MkBox (Succ (Zero))))))
