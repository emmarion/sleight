; needs: list
; error: type mismatch
; A first-class match's Matchable carries the type's full constructor list in its
; type, so a one-constructor Matchable parameter cannot receive a two-constructor
; type's real Matchable: exhaustiveness cannot be dodged this way (sections 17, 19).

(def-adts $ Two : -> Type enum
  (many A : (many (Nat) n) -> (Two))
  (many B : (many (Nat) n) -> (Two)))

(def-lvl X)
(def-fns X $ many f : (erased (TyCtor -> Type) T)
    (many (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n)
  (match many x (((Nat) r)) ((C n) n)))

(f Two A (matchable-of Two) (A (Zero)))
