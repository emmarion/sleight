; expect: (Zero)
; Resolving by spelling holds inside a branch that has equated two literals: each still fetches its own
; proof, and two spellings for one Nat refute the branch.

(def-adts (Tag : ((Nat) n) -> Type
  enum
  (many TA : -> (Tag 0))
  (many TB : -> (Tag 1))))

(def-lvl Y)
(def-fns Y $ many clash : (erased (Nat) n) (erased (Numeral (BZ) n) v0) (erased (Numeral (B1 (BZ)) n) v1) ->
    (many (False) f)
  (match erased v0 _
    ((NZ) (match erased v1 _ (absurd NZ) (absurd N1) (absurd N2)))
    (absurd N1)
    (absurd N2)))

(def-lvl Z)
(let (erased pz) (prove-predates Y Z))

(def-fns Z $ many only-a : (many (Tag 0) t) -> (many (Nat) n)
  (match many t (((Nat) r))
    ((TA) (Zero))
    (absurd (TB) (clash (predates pz) 0 (numeral-of 0) (numeral-of 1)))))

(only-a (TA))
