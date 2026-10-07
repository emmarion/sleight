; error: type mismatch
; Shadowing Void after explode is defined cannot feed the new, inhabited Void to
; it: explode captured the original, empty Void by entry identity (section 19), so
; (Sole) is a value of the second Void and not of explode's parameter type. The
; second declaration is the shadowing, deliberate here and recorded by the
; ; warns: lines at the end of the file.

(def-adts $ (Void : -> Type) enum)
(def-lvl X)
(def-fns X $ (many absurd explode : (erased Type A) (many (Void) f) -> (many A a)) f)

(def-adts $ (Void : -> Type) enum (many Sole : -> (Void)))
(def-lvl Y)
(let ((erased p)) (prove-predates explode Y))
(def-fns Y $ (many boom : -> (many (Nat) n))
  (explode (predates p) (Nat) (Sole)))
(boom)
; warns: tests/shadow_false_capture.sl:12:13: warning: declaration of `Void` shadows a previous binder
; warns: tests/shadow_false_capture.sl:8:13: note: shadowed binder is here
