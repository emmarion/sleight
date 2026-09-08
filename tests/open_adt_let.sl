; expect: (Succ (Zero))
; An open's extent is the rest of the containing expression, discarded exactly when the entries minted beside
; it are (proposals/matchable-newtype-opening.md): a let's right-hand side retains both, so the open inside the
; right-hand side still serves the match after the let. That match dispatches nothing, its scrutinee erased;
; the entry the open bound went out of scope with the right-hand side, as a let-bound variable does, so a
; match that would read it at runtime is refused (tests/open_adt_let_bad.sl).

(def-adts $ Box : -> Type enum (many MkBox : (many (Nat) n) -> (Box)))
(def-lvl X)
(def-fns X $ many open : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (many (Matchable enum T (many C)) m)
    (many (T) x) -> (many (Nat) n)
  (let (many k) (open-adt many m) (match many x (((Nat) r)) ((C n) n)))
  (match erased x (((Nat) r)) ((C n) (Succ k))))
(open Box MkBox (matchable-of Box) (MkBox (Zero)))
