; expect: 0
; A binder may hide a special form or an annotation token as readily as anything else
; (section 19), and that is the case the warning is most worth finding: the scope it
; opens cannot write the marker any more. A built-in has no position of its own, so
; the message says so in place of pointing at one.

(def-adts $ (Cell2 : -> Type)
  enum
  (many MkCell2 : (many (Nat) head) (many (Nat) tail) -> (Cell2)))

(def-lvl at)

(def-fns at $ (many first : (many (Cell2) c) -> (many (Nat) r))
  (match many c _
    ((MkCell2 head tail) head)))

(let ((many values)) (Zero))

(first (MkCell2 values (Succ values)))
; warns: tests/shadow_builtin_warn.sl:9:37: warning: declaration of `tail` shadows a built-in
; warns: tests/shadow_builtin_warn.sl:11:10: warning: declaration of `at` shadows a built-in
; warns: tests/shadow_builtin_warn.sl:15:20: warning: declaration of `tail` shadows a built-in
; warns: tests/shadow_builtin_warn.sl:15:20: warning: unused `tail`; write `_` in its place
; warns: tests/shadow_builtin_warn.sl:17:7: warning: declaration of `values` shadows a built-in
