; expect: tick
; expect: tick
; expect: done
; Step performs nothing and hands its continuation back to the driver, so a program can iterate without an
; effect; and now that WriteOut carries a function too, a loop can be written with output alone. Both loops
; defer to the driver rather than recursing: the continuation is a level-P closure over the decremented
; count, and P comes after the loop's own level, so neither function can call it. The unbounded iteration
; is the driver's, as it already was for a ReadLine loop.

(def-lvl P1)
(def-lvl P0)
(def-lvl P)
(let (many d0) (lt-dec 0 u8-modulus))
(comptime-match d0 (Yes za0 zb0 zp0))
(let (many code0) (MkU8 0 zp0))
(let (erased p1-p0) (prove-predates P1 P0))
(let (erased p1-p) (prove-predates P1 P))
(let (erased p0-p) (prove-predates P0 P))
(let (erased th-p1) (prove-predates thunk-lvl P1))

(def-fns P1 $ many shout : (subterm many (Nat) n) -> (many (IO P) next)
  (match many n _
    ((Zero) (WriteOut P "done\n" (thunk (predates th-p1) _ _ (Exit P code0))))
    ((Succ m)
      (def-fns P $ many again : -> (many (IO P) next)
        (shout (predates p1-p) m))
      (WriteOut P "tick\n" again))))

(def-fns P0 $ many settle : (subterm many (Nat) n) -> (many (IO P) next)
  (match many n _
    ((Zero) (shout (predates p1-p0) 2))
    ((Succ m)
      (def-fns P $ many again : -> (many (IO P) next)
        (settle (predates p0-p) m))
      (Step P again))))

(settle 3)
