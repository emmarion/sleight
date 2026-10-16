(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))

(def-fns _ $ (many count : (subterm many (List (Slot)) xs) -> (many (Nat) n))
  (let-match many xs (Cons _ _ rest) ((Nil _) 0))
  (Succ $ notail $ count rest))

(def-fns _ $ (many run : -> (many (List (Nat)) out))
  (let ((many a)) (MkBox 1))
  (let ((many b)) (MkBox 2))
  (let ((unique t0)) (MkSlots (Cons _ (slot-of b) $ Cons _ (slot-of a) $ Nil _)))
  (let ((erased _) (many r) (unique t1)) (slots-intern _ t0 (slot-of a)))
  (let ((many i)) (match many r (((Nat) k)) ((SlotExisting _ _ i _) i) ((SlotAdded _ _ i _) 99)))
  (let ((erased _) (many r2) (unique t2)) (slots-intern _ t1 (slot-of b)))
  (let-match unique t2 (MkSlots ls))
  (Cons _ i $ Cons _ (count ls) $ Nil _))

run
; expect: (Cons _ 0 $ Cons _ 2 $ Nil _)
; warns: tests/slots_view.sl:10:23: warning: application of `MkSlots`: builds a `Slots` through its model, O(n); start one with `slots-new`
; warns: lib/prelude.sl:1530:1: note: `;! warn` for `MkSlots` is here
; warns: tests/slots_view.sl:14:3: warning: match on `Slots`: copies the whole table out, O(n); use `slots-find`, `slots-intern` or `slots-length`
; warns: lib/prelude.sl:1531:1: note: `;! warn` for `Slots` is here
