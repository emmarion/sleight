(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

;! warn MkBox boxing is slow
;! suppress warn MkBox
;! file "claimed/box.sl"
(let ((many a)) (MkBox 1))
;! restore warn MkBox
(def-fns _ $ (many two : -> (many (Box) r))
  ;! file "claimed/two.sl"
  (MkBox 2))
(two)
; expect: (MkBox 2)
; warns: claimed/two.sl:1:4: warning: application of `MkBox`: boxing is slow
; warns: tests/file_pragma.sl:5:1: note: `;! warn` for `MkBox` is here
