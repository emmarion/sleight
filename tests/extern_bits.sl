; expect: (Cons _ 6 $ Cons _ 1 $ Cons _ 0 $ Cons _ 1 $ Cons _ 6 $ Cons _ 9 $ Cons _ 0 $ Cons _ 6 $ Cons _ 1 $ Cons _ 1 $ Cons _ 0 $ Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 1 $ Cons _ 0 $ Nil _)
; bit-length through BitLength, which BitCons builds from the low bit and its Lt (Zero) n premise stops at
; zero, and bit-test through BitAt, Bit0 past the length; their U62 versions under bounds, the delegates without
; proofs, and the functionality lemmas. Each runs once at elaboration and once inside a function.

(def-fns _ $ (many bit-nat : (many (Bit) x) -> (many (Nat) r))
  (match many x _ ((Bit0) 0) ((Bit1) 1)))

(let ((erased p43)) (lt-trans _ _ _ (prove-literal-lt 43 u8-modulus) u8-below-u62))
(let ((erased k5)) (lt-weaken _ _ $ lt-trans _ _ _ (prove-literal-lt 5 eight) (eight-lt-sixty-two)))
(let ((erased k2)) (lt-weaken _ _ $ lt-trans _ _ _ (prove-literal-lt 2 eight) (eight-lt-sixty-two)))

(let ((many l43) (erased bl43)) (bit-length 43))
(let ((erased (Eq (Nat) l43 l43) _)) (bit-length-fn _ _ _ bl43 bl43))
(let ((many b0) (erased ba0)) (bit-test 43 0))
(let ((erased (Eq (Bit) b0 b0) _)) (bit-at-fn _ _ _ _ ba0 ba0))

(def-lvl A)
(def-fns A $ (many bits : -> (many (List (Nat)) out))
  (let ((many l1) (erased _)) (bit-length 1))
  (let ((many l0) (erased _)) (bit-length 0))
  (let ((many lu) (erased _)) (u62-bit-length 43 p43))
  (let ((many ln)) (nat-bit-length 300))
  (let ((many t1) (erased _)) (bit-test 43 1))
  (let ((many t2) (erased _)) (bit-test 43 2))
  (let ((many t5) (erased _)) (bit-test 43 5))
  (let ((many t40) (erased _)) (bit-test 43 40))
  (let ((many tz) (erased _)) (bit-test 0 3))
  (let ((many u5) (erased _)) (u62-bit-test 43 5 p43 k5))
  (let ((many u2) (erased _)) (u62-bit-test 43 2 p43 k2))
  (let ((many tn)) (nat-bit-test 300 3))
  (Cons _ l43 $ Cons _ (bit-nat b0) $ Cons _ l0 $ Cons _ l1 $ Cons _ lu $ Cons _ ln $ Cons _ (bit-nat tz) $ Cons _ (nat-bit-length 32) $
    Cons _ (bit-nat t1) $ Cons _ (bit-nat t5) $ Cons _ (bit-nat t2) $ Cons _ (bit-nat u5) $ Cons _ (bit-nat u2) $ Cons _ (bit-nat t40) $
    Cons _ (bit-nat tn) $ Cons _ (bit-nat $ nat-bit-test 300 0) $ Nil _))

bits
