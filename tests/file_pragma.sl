(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

;! warn MkBox boxing is slow
;! suppress warn MkBox
(let ((many _)) (MkBox 1))
;! file "claimed/box.sl"
(let ((many b)) (MkBox 2))
b
;! file "claimed/two.sl"
(def-fns _ $ (many two : -> (many (Box) r))
  (MkBox 3))
(two)
; expect: (MkBox 2)
; expect: (MkBox 3)
; warns: claimed/box.sl:1:18: warning: application of `MkBox`: boxing is slow
; warns: tests/file_pragma.sl:5:1: note: `;! warn` for `MkBox` is here
; warns: claimed/two.sl:2:4: warning: application of `MkBox`: boxing is slow
; warns: tests/file_pragma.sl:5:1: note: `;! warn` for `MkBox` is here
