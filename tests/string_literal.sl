; expect: 2
; A string literal is an opaque Const String; comptime-match reads its value.

(def-fns _ $ (many len : (subterm many (String) s) -> (many (Nat) n))
  (match many s _
    ((SNil) (Zero))
    ((SCons c rest) (Succ (notail $ len (subterm _) rest)))))

(let ((many s)) "a\"")
(comptime-match many s (SCons c rest))
(comptime-match many rest (SCons d tl))
(comptime-match many tl (SNil))
(len s)
