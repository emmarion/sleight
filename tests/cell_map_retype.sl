; needs: cell_rev_inplace
; expect: (UCons _ (MkTag 0) $ UCons _ (MkTag 1) $ UNil _)
; A map that changes the element type and allocates nothing. The cell a unique destructure hands back is
; tied to its constructor but not to the type arguments, so UCons's cell can be reinvoked at (ULst (Tag))
; where it was built at (ULst (Nat)); Tag is a newtype, so its wrapper is its field's word (DESIGN.md
; section 38) and the whole map reuses the spine in place.

(def-adts $ Tag : -> Type
  enum newtype
  (many MkTag : (many (Nat) n) -> (Tag)))

(def-fns _ $ many map-retype : (subterm unique (ULst (Nat)) xs) -> (unique (ULst (Tag)) r)
  (match unique xs _
    ((UNil _ c) (UNil _))
    ((UCons _ hd tl cell)
      (let (unique tl2) (map-retype tl))
      (cell _ (MkTag hd) tl2))))

(def-fns _ $ many run-retype : -> (many (ULst (Tag)) r)
  (let (unique xs) (UCons _ 0 (UCons _ 1 (UNil _))))
  (share (map-retype xs)))
run-retype
