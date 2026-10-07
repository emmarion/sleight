; expect: 1
; Shadowing is legal (section 19) and warns at every binder that hides a name already
; in scope. Each kind of binder is exercised once here: a level's name, a function's
; name, a match branch's field over the function's own parameter, and a let binder
; over an earlier one. The ; warns: lines at the end of the file are what that earns,
; and they sit at the end because each names a line of this file.

(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) v) (many (Nat) w) -> (Box)))

(def-lvl K)
(def-lvl K)

(def-fns K $ (many pick : (many (Box) b) (many (Nat) w) -> (many (Nat) r))
  (match many b _
    ((MkBox v w) w)))

(def-fns K $ (many pick : (many (Nat) n) -> (many (Nat) r)) n)

(let ((many q)) (Zero))
(let ((many q)) (Succ q))

(pick q)
; warns: tests/shadow_warn.sl:13:10: warning: declaration of `K` shadows a previous binder
; warns: tests/shadow_warn.sl:12:10: note: shadowed binder is here
; warns: tests/shadow_warn.sl:17:15: warning: declaration of `w` shadows a previous binder
; warns: tests/shadow_warn.sl:15:42: note: shadowed binder is here
; warns: tests/shadow_warn.sl:19:14: warning: declaration of `pick` shadows a previous binder
; warns: tests/shadow_warn.sl:15:14: note: shadowed binder is here
; warns: tests/shadow_warn.sl:22:7: warning: declaration of `q` shadows a previous binder
; warns: tests/shadow_warn.sl:21:7: note: shadowed binder is here
