(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

;! warn MkBox boxing is slow   
;! warn Box unboxing is slow

(let ((many b)) (MkBox 3))

(let ((many mk)) MkBox)

(let ((many c)) (mk 4))

(comptime-match many c (MkBox four))

(def-fns _ $ (many unbox : (many (Box) x) -> (many (Nat) n))
  (match many x _ ((MkBox n) n)))

(def-fns _ $ (many unbox-let : (many (Box) x) -> (many (Nat) n))
  (let-match many x (MkBox n))
  n)

(def-fns _ $ (erased rebox : (many (Box) x) -> (many (Box) y))
  (match erased x _ ((MkBox n) (MkBox n))))

(def-fns _ $ (many rebox-erased : (many (Box) x) -> (many (Box) y))
  (let ((erased z)) (MkBox 5))
  x)

(unbox-let $ rebox-erased (MkBox (unbox b)))
; expect: 3
; warns: tests/warn_pragma.sl:8:18: warning: application of `MkBox`: boxing is slow
; warns: tests/warn_pragma.sl:5:1: note: `;! warn` for `MkBox` is here
; warns: tests/warn_pragma.sl:12:18: warning: application of `mk`: boxing is slow
; warns: tests/warn_pragma.sl:5:1: note: `;! warn` for `mk` is here
; warns: tests/warn_pragma.sl:14:1: warning: match on `Box`: unboxing is slow
; warns: tests/warn_pragma.sl:6:1: note: `;! warn` for `Box` is here
; warns: tests/warn_pragma.sl:17:3: warning: match on `Box`: unboxing is slow
; warns: tests/warn_pragma.sl:6:1: note: `;! warn` for `Box` is here
; warns: tests/warn_pragma.sl:20:3: warning: match on `Box`: unboxing is slow
; warns: tests/warn_pragma.sl:6:1: note: `;! warn` for `Box` is here
; warns: tests/warn_pragma.sl:30:28: warning: application of `mk`: boxing is slow
; warns: tests/warn_pragma.sl:5:1: note: `;! warn` for `mk` is here
