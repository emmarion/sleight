; expect: 4
; warns: tests/compile_warn.sl:17:1: warning: a literal
; warns: tests/compile_warn.sl:22:1: warning: by hand
; warns: tests/compile_warn.sl:24:1: warning: run position
; warns: tests/compile_warn.sl:26:1: warning: by hand
; warns: tests/compile_warn.sl:27:1: warning: u
; warns: tests/compile_warn.sl:30:3: warning: a body
; warns: tests/compile_warn.sl:32:13: warning: a branch
; warns: tests/compile_warn.sl:33:15: warning: another branch
; warns: tests/compile_warn.sl:35:3: warning: an erased body
; warns: tests/compile_warn.sl:38:3: warning: an at-function
; warns: tests/compile_warn.sl:40:19: warning: an erased right-hand side
; `compile-warn` takes any Const, non-erased String: a literal, one built by hand, one computed in run position,
; an alias of one, or a unique one shared. It warns wherever it is elaborated, erased code and at-functions
; included, and elaboration goes on.

(compile-warn "a literal")
;! suppress warn SCons
(let ((many built)) (SCons #\b $ SCons #\y $ SCons #\space $ SCons #\h $ SCons #\a $ SCons #\n $ SCons #\d $ SNil))
(let ((unique once)) (SCons #\u $ SNil))
;! restore warn SCons
(compile-warn built)
(let ((many joined)) (str-append "run " "position"))
(compile-warn joined)
(let ((many alias)) built)
(compile-warn alias)
(compile-warn (share once))

(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (compile-warn "a body")
  (match many n _
    ((Zero) (compile-warn "a branch") n)
    ((Succ k) (compile-warn "another branch") k)))
(def-fns _ $ (erased g : (many (Nat) n) -> (many (Nat) m))
  (compile-warn "an erased body")
  n)
(def-fns _ $ (many at h : (many (Nat) n) -> (many n is m at n))
  (compile-warn "an at-function")
  n)
(let ((erased e)) (compile-warn "an erased right-hand side") (f 5))
(f 5)
