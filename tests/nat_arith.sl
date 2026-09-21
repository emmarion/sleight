; expect: (Cons _ 12 $ Cons _ 5 $ Cons _ 3 $ Cons _ 12 $ Cons _ 5 $ Cons _ 3 $ Cons _ 15 $ Cons _ 3 $ Cons _ 2 $ Cons _ 3 $ Cons _ 2 $ Nil _)
; The extern Nat arithmetic beyond add and nat-mod: mul, sub under a bound proof, div and divmod under a
; positive divisor, each once at elaboration, where the value is embedded, and once inside a thunk, where the
; implementation runs.

(let (many bound) (lt-dec 4 (Succ 9)))
(comptime-match many bound (Yes ba bb le))
(let (many positive) (lt-dec (Zero) 5))
(comptime-match many positive (Yes pa pb pos))

(let (many twelve) (erased mp) (mul 3 4))
(let (many five) (erased sp) (sub 9 4 le))
(let (many three) (erased m) (erased r) (erased mm) (erased a) (erased p) (div 17 5 pos))
(let (many three2) (many two) (erased dm) (erased dmm) (erased da) (erased dp) (divmod 17 5 pos))

(def-lvl A)
(def-fns A $ many arith : -> (many (List (Nat)) r)
  (let (many x) (erased xp) (mul 3 4))
  (let (many y) (erased yp) (sub 9 4 le))
  (let (many z) (erased zm) (erased zr) (erased zmm) (erased za) (erased zp) (div 17 5 pos))
  (let (many w) (nat-mul 5 3))
  (let (many dq) (many dr) (erased em) (erased emm) (erased ea) (erased ep) (divmod 17 5 pos))
  (Cons (Nat) twelve (Cons (Nat) five (Cons (Nat) three (Cons (Nat) x (Cons (Nat) y (Cons (Nat) z (Cons (Nat) w (Cons (Nat) three2 (Cons (Nat) two (Cons (Nat) dq (Cons (Nat) dr (Nil (Nat))))))))))))))

arith
