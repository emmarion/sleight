; expect: (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))
; Extern functions over numerals in the final function's code: with the FFI stripped, the prelude's models run.

(def-lvl T)
(let (erased ut) (prove-predates u8-lvl T))
(def-fns T $ many main : -> (many (Nat) n)
  (u8-to-nat (predates ut) (u8-add (predates ut) (nat-to-u8 (predates ut) 3) (nat-to-u8 (predates ut) 4))))

main
