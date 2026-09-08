; error: contradicts what is open
; Two Matchables that share a constructor but cannot unify -- their constructor lists differ in length --
; contradict each other, so the second open-adt is refused (tests/open_absurd_clash.sl takes the other form).

(def-lvl X)
(def-fns X $ many f : (erased (TyCtor -> Type) T) (erased (TyCtor -> Type) U)
    (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m1)
    (erased (Matchable enum U (many C)) m2) -> (many (Nat) n)
  (open-adt erased m1)
  (open-adt erased m2)
  (Zero))
f
