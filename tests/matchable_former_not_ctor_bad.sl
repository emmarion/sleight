; error: `k` is not a value constructor
; A Matchable entry must be a value constructor where the type is written,
; so an entry of type (Nat) is refused there, before any fact could rewrite
; it into an application (section 24).

(def-fns _ $ (many f : (erased (TyCtor -> Type) T) (erased (Nat) k) (erased (Matchable enum T (many k)) m)
    (erased (Nat) j) (erased (Eq (Nat) k (Succ j)) e) (erased (T) x) -> (many (Nat) n))
  (open-adt erased m)
  (let-match erased e (Refl _ _))
  (match erased x (((Nat) r))))
(Zero)
