; error: is not a strict subterm of
; A field a unique match binds is not a subterm of the cell it came out of. The cell is reached through
; Cell, a type former, which section 8 makes opaque; the field is a subterm of the scrutinee instead
; (tests/cell_subterm.sl).

(def-adts $ Box : -> Type enum (many B : (many (Nat) n) -> (Box)))
(def-fns _ $ many probe : (unique (Box) x) -> (many (Nat) r)
  (match unique x (((Nat) r))
    ((B n c)
      (let (erased p) (prove-subterm n c))
      n)))
