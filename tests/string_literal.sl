; expect: (Succ (Succ (Zero)))
; A string literal is its characters consed up, transparent like a character literal.

(def-fns _ $ many len : (subterm many (String) s) -> (many (Nat) n)
  (match many s _
    ((SNil) (Zero))
    ((SCons c rest) (Succ (len (subterm _) rest)))))

(let (many s) "a\"")
(comptime-match s (SCons c rest))
(comptime-match rest (SCons d tail))
(comptime-match tail (SNil))
(len s)
