; expect: 2
; Unopened means opaque, upward too (DESIGN.md section 8): two type constructors are told
; apart by their Matchables, so with m unopened T unifies with (Nat) and the IsNat branch must be written,
; while with m opened T's constructors meet Nat's, D's signature differs from Succ's, and IsNat is refuted.

(def-adts $ (Shape : (Type T) -> Type)
  enum
  (many IsNat : -> (Shape (Nat)))
  (many IsBool : -> (Shape (Bool))))
(def-lvl X)
(def-fns X $ (many opaque : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) _m) (many (Shape (T)) s) -> (many (Nat) n))
  (match many s (((Nat) r))
    ((IsNat) (Zero))
    ((IsBool) (Succ (Zero)))))
(def-fns X $ (many told : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m) (many (Shape (T)) s) -> (many (Nat) n))
  (open-adt erased m)
  (match many s (((Nat) r))
    (absurd IsNat)
    ((IsBool) (Succ (Zero)))))
(nat-add (opaque Bool BTrue BFalse (matchable-of Bool) (IsBool)) (told Bool BTrue BFalse (matchable-of Bool) (IsBool)))
