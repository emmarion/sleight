; expect: 3
; WARNINGS.md 10: `settled-of` references its name, from an erased position at `erased`.
; The ; warns: line at the end of the file names a line of this file.

(def-fns _ $ (many value : -> (many (Nat) r))
  (let ((many kept)) 3)
  (let ((many h)) (settled-of many kept))
  (settled-value _ _ h))
(def-fns _ $ (many type : -> (many (Settled (MErased) Type (Nat)) r))
  (let ((many ghost)) 4)
  (settled-type _ _ _ (settled-of erased ghost)))
(value)
; warns: tests/unused_settled_of_warn.sl:10:9: warning: `ghost` is referenced only in erased positions; declare it `erased`
