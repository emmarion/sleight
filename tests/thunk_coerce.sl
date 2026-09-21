; needs: list map coerce
; expect: (Cons _ 2 $ Cons _ 1 $ Nil _)
; A coerce, a delegate and a factory-made map in the final function's code.

(def-lvl T)
(let (erased vt) (prove-predates V T))
(let (erased mlt) (prove-predates ML T))
(def-fns T $ many main : -> (many (List (Nat)) ns)
  (map-nat (predates mlt) (Nat) (Nat) inc (unwrap-all (predates vt) ms)))

main
