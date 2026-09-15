; expect: <function coexist>
; An opened Newtype beside an opened Matchable marking its constructor phantom is recorded, not refused
; (section 19, SPEC-REVIEW 29). Such a pair is not dead code by inhabitation: a function is also called in
; an erased position, where a many parameter may hold a phantom constructor (section 20), as `through`
; is below with G at C. What keeps the pair inert is that a Newtype is minted for the wrapper alone, so
; nothing of nt's type can be supplied for a phantom C, and that an erased body's matches are erased,
; where a phantom constructor's branch is an ordinary one (section 12).

(def-adts $ U : -> Type
  union newtype
  (many W : (many (Nat) n) -> (U))
  (erased G : (erased (Nat) n) -> (U)))

(def-lvl X)
(def-fns X $ many through : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) D)
    (many (ValCtor (erased (Nat) n) -> (T)) C)
    (erased (Matchable union T (many D) (erased C)) m)
    (erased (T) x) -> (erased (Nat) r)
  (open-adt erased m)
  (match erased x (((Nat) r)) ((D n) n) ((C n) n)))

(let (erased r) (through U W G (matchable-of U) (G (Zero))))

(def-fns X $ many coexist : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Matchable enum T (erased C)) m)
    (erased (Newtype C) nt) -> (many (Nat) r)
  (open-adt erased m)
  (open-adt erased nt)
  (Zero))

coexist
