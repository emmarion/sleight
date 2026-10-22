; expect: 0
; Opening a Matchable unifies it with every opened one that heads its type constructor, minting the facts
; that takes (DESIGN.md section 8): m1 and m2 both name T, so opening both equates D with E, which the
; returned Refl relies on.

(def-adts $ (Two : -> Type) enum (many A : -> (Two)) (many B : -> (Two)))
(def-lvl X)
(def-fns X $ (many same : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D) (erased (ValCtor -> (T)) E)
    (erased (Matchable enum T (many C) (many D)) m1)
    (erased (Matchable enum T (many C) (many E)) m2) ->
    (erased (Eq (ValCtor -> (T)) D E) p) (many (Nat) n))
  (open-adt erased m1)
  (open-adt erased m2)
  (values (Refl _ D) (Zero)))
(let ((erased _) (many n)) (same Two A B B (matchable-of Two) (matchable-of Two)))
n
