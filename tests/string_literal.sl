; expect: 2
; A string literal is its characters consed up, transparent like a character literal.

(def-fns _ $ many len : (subterm many (String) s) -> (many (Nat) n)
  (match many s _
    ((SNil) (Zero))
    ((SCons c rest) (Succ (len (subterm _) rest)))))

(let (many s) "a\"")
(comptime-match many s (SCons c rest))
(comptime-match many rest (SCons d tail))
(comptime-match many tail (SNil))
(len s)
