; A final value is printed by the facts in force where it stands, by the driver and by an extracted program
; alike: `T` is opaque when `v` is printed, and a later file's `let-match` that shows it to be `String` does
; not change what the first printed.
(def-fns _ $ (many conv : (erased Type A) (many A a) -> (erased Type T) (many T v) (erased (Eq Type T A) p))
  (values A a (Refl _ _)))
(let ((erased T) (many v) (erased p)) (conv (String) "abc"))
(def-fns _ $ (many get : -> (many T r))
  v)
v
;! file "final/thunk.sl"
get
;! file "final/known.sl"
(let-match erased p (Refl _ _))
v
; expect: _
; expect: _
; expect: "abc"
