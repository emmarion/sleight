; expect: <function held>
; Facts can be held before they explode (proposals/matchable-newtype-opening.md): with m unopened, matching
; Refl equates C with D by minting a fact, and open-absurd then cashes the contradiction in, producing the
; branch's declared result from no value. With m opened first, the same branch is refuted structurally.

(def-lvl X)
(def-fns X $ many held : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) C)
    (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m)
    (erased (Eq (T) (C) (D)) p) -> (many (Nat) n)
  (match erased p (((Nat) r))
    ((Refl A x) (open-absurd m _))))

(def-fns X $ many refuted : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) C)
    (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m)
    (erased (Eq (T) (C) (D)) p) -> (many (Nat) n)
  (open-adt erased m)
  (match erased p (((Nat) r))
    (absurd Refl)))

held
