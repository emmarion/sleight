(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))
(def-lvl X)
(def-fns X $ (many keys-of : (erased (TyCtor (Type A) ((List (SlotItem A)) xs) -> Type) T)
    (many (ValCtor (erased Type A) (many (List (SlotItem A)) xs) -> (T A xs)) K)
    (many (Matchable enum extern T (many K)) m)
    (erased Type A) (erased (List (SlotItem A)) xs)
    (many (T A xs) s) -> (many (Nat) n))
  (open-adt many m)
  (match many s (((Nat) r))
    ((K _ l) (match many l _ ((Nil _) 0) ((Cons _ _ _) 1)))))
(def-lvl Y)
(let ((erased xy)) (prove-predates X Y))
(def-fns Y $ (many run : -> (many (Nat) out))
  (let ((unique t0)) (slots-new (Box)))

  (keys-of Slots MkSlots (matchable-of Slots) _ _ (share t0)))
run
; expect: 0
; warns: tests/held_slots.sl:9:4: warning: lopsided `match`; flatten it with a `let-match` on `K`
; warns: tests/held_slots.sl:4:5: warning: `K` is referenced only in erased positions; declare it `erased`, or rename it `_K`
