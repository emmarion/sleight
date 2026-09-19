; expect: 7
; Extern functions over numerals in the final function's code: with the FFI stripped, the prelude's models run.

(def-lvl T)
(let (erased ut) (prove-predates u8-lvl T))
(let (many d3) (lt-dec 3 u8-modulus))
(comptime-match many d3 (Yes za3 zb3 zp3))
(let (many u3) (MkU8 3 zp3))
(let (many d4) (lt-dec 4 u8-modulus))
(comptime-match many d4 (Yes za4 zb4 zp4))
(let (many u4) (MkU8 4 zp4))

(def-fns T $ many main : -> (many (Nat) n)
  (let (many s) (u8-add (predates ut) u3 u4))
  (let-match many s (MkU8 sn sq))
  (coerce s (coercible-sym (coercible-wrap MkU8 sn sq))))

main
