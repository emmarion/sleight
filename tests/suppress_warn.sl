(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

;! warn MkBox boxing is slow

;! suppress warn MkBox the next two are fine
(let ((many a)) (MkBox 1))
(let ((many mk)) MkBox)
(let ((many b)) (mk 2))
;! restore warn MkBox

(def-fns _ $ (many three : -> (many (Box) r))
  (let ((many x))
    ;! suppress warn MkBox
    (MkBox 3))
  ;! restore warn MkBox
  (MkBox 3))

;! suppress warn MkBox
(let ((many c)) (Zero))
;! restore warn MkBox

;! suppress warn Nowhere
(let ((many d)) (mk 4))
;! restore warn Nowhere

;! suppress warn MkBox to the end of the file
(mk 5)
; expect: (MkBox 5)
; warns: tests/suppress_warn.sl:18:4: warning: application of `mk`: boxing is slow
; warns: tests/suppress_warn.sl:5:1: note: `;! warn` for `mk` is here
; warns: tests/suppress_warn.sl:25:18: warning: application of `mk`: boxing is slow
; warns: tests/suppress_warn.sl:5:1: note: `;! warn` for `mk` is here
; warns: tests/suppress_warn.sl:20:1: warning: `;! suppress warn` for `MkBox` silenced nothing
; warns: tests/suppress_warn.sl:24:1: warning: `;! suppress warn` for `Nowhere` silenced nothing
