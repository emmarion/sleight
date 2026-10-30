(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) v) -> (Box)))

(def-fns _ $ (many count : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (let-match many xs (Cons _ _ rest) ((Nil _) 0))
  (Succ $ notail $ count _ rest))

(def-fns _ $ (many run : -> (many (List (Nat)) out))
  (let ((many a)) (MkBox 1))
  (let ((many b)) (MkBox 2))
  (let ((unique t0)) (MkSlots _ (Cons _ (MkSlotItem _ _ _ (place-at-many _ b)) $ Cons _ (MkSlotItem _ _ _ (place-at-many _ a)) $ Nil _)))
  (let ((erased _) (many r) (unique t1)) (slots-intern _ _ t0 _ _ (place-at-many _ a)))
  (let ((many i)) (match many r (((Nat) k)) ((SlotExisting _ _ _ _ _ i _) i) ((SlotAdded _ _ _ _ _ _ _) 99)))
  (let ((erased _) (many _) (unique t2)) (slots-intern _ _ t1 _ _ (place-at-many _ b)))
  (let-match unique t2 (MkSlots _ ls))
  (Cons _ i $ Cons _ (count _ ls) $ Nil _))

run
; expect: (Cons _ 0 $ Cons _ 2 $ Nil _)
; warns: tests/slots_view.sl:10:23: warning: application of `MkSlots`: builds a `Slots` through its model, O(n); start one with `slots-new`
; warns: lib/prelude.sl:1759:1: note: `;! warn` for `MkSlots` is here
; warns: tests/slots_view.sl:14:3: warning: match on `Slots`: copies the whole table out, O(n); use `slots-find`, `slots-intern` or `slots-length`
; warns: lib/prelude.sl:1760:1: note: `;! warn` for `Slots` is here
