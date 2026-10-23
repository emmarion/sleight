(let ((many spec-s60) (erased spec-s60m)) (mul (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) ten))
(let-match erased (mul-fn _ _ _ _ spec-s60m sixty-mul) (Refl _ _))
(let ((many spec-s62) (erased spec-s62a)) (add spec-s60 (Succ (Succ (Zero)))))
(let-match erased (add-fn _ _ _ _ spec-s62a sixty-two-add) (Refl _ _))
(let ((many u62m) (erased spec-u62m-pow2) (erased _)) (pow2 spec-s62))
(let-match erased (pow2-fn _ _ _ spec-u62m-pow2 u62-modulus-pow2) (Refl _ _))
(let ((many spec-u62m-cmp)) (nat-cmp 4611686018427387904 u62m))
(comptime-match many spec-u62m-cmp (CEq _ _ _))
(let ((many max-array-length)) 18014398509481984)
(let ((erased (Lt max-array-length u62-modulus) max-array-length-below-u62))
  (prove-literal-lt 18014398509481984 4611686018427387904))

(def-adts
  ((Fold : ((U8) x) ((U8) y) -> Type)
    enum
    (many FoldUpper : (erased (Nat) n) (erased (Lt n u8-modulus) p) (erased (Nat) m) (erased (Lt m u8-modulus) q)
        (erased (Lt 64 n) lo) (erased (Lt n 91) hi) (erased (Add 32 n m) lower)
        -> (Fold (MkU8 n p) (MkU8 m q)))
    (many FoldBelow : (erased (Nat) n) (erased (Lt n u8-modulus) p) (erased (Lt n 65) lo)
        -> (Fold (MkU8 n p) (MkU8 n p)))
    (many FoldAbove : (erased (Nat) n) (erased (Lt n u8-modulus) p) (erased (Lt 90 n) hi)
        -> (Fold (MkU8 n p) (MkU8 n p)))))

(def-adts
  ((Apart : ((U8) x) ((U8) y) -> Type)
    enum
    (many ApartLt : (erased (Nat) n) (erased (Lt n u8-modulus) p) (erased (Nat) m) (erased (Lt m u8-modulus) q)
        (erased (Lt n m) lt) -> (Apart (MkU8 n p) (MkU8 m q)))
    (many ApartGt : (erased (Nat) n) (erased (Lt n u8-modulus) p) (erased (Nat) m) (erased (Lt m u8-modulus) q)
        (erased (Lt m n) gt) -> (Apart (MkU8 n p) (MkU8 m q)))))

(def-adts
  ((Cost : ((U8) x) ((U8) y) ((Nat) c) -> Type)
    enum
    (many CostSame : (erased (U8) x) -> (Cost x x 0))
    (many CostCase : (erased (U8) x) (erased (U8) y) (erased (U8) f)
        (erased (Fold x f) fx) (erased (Fold y f) fy) (erased (Apart x y) apart) -> (Cost x y 1))
    (many CostOther : (erased (U8) x) (erased (U8) y) (erased (U8) f) (erased (U8) g)
        (erased (Fold x f) fx) (erased (Fold y g) fy) (erased (Apart f g) apart) -> (Cost x y 2))))

(def-adts
  ((AtMost : ((Nat) d) ((List (Nat)) cs) -> Type)
    enum
    (many AtMostNil : (erased (Nat) d) -> (AtMost d (Nil (Nat))))
    (many AtMostCons : (erased (Nat) d) (erased (Nat) c) (erased (List (Nat)) cs)
        (erased (Le d c) le) (erased (AtMost d cs) rest) -> (AtMost d (Cons (Nat) c cs)))))

(def-adts
  ((Least : ((List (Nat)) cs) ((Nat) d) -> Type)
    enum
    (many MkLeast : (erased (List (Nat)) cs) (erased (Nat) d) (erased (Nat) i)
        (erased (Nth (Nat) cs i d) member) (erased (AtMost d cs) below) -> (Least cs d))))

(def-adts
  ((Dist : ((List (U8)) xs) ((List (U8)) ys) ((Nat) d) -> Type)
    enum
    (many DistNil : -> (Dist (Nil (U8)) (Nil (U8)) 0))
    (many DistDelete : (erased (U8) x) (erased (List (U8)) xs)
        (erased (Nat) a) (erased (Dist xs (Nil (U8)) a) rest) (erased (Nat) d) (erased (Add 2 a d) sum)
        -> (Dist (Cons (U8) x xs) (Nil (U8)) d))
    (many DistInsert : (erased (U8) y) (erased (List (U8)) ys)
        (erased (Nat) a) (erased (Dist (Nil (U8)) ys a) rest) (erased (Nat) d) (erased (Add 2 a d) sum)
        -> (Dist (Nil (U8)) (Cons (U8) y ys) d))
    (many DistStep : (erased (U8) x) (erased (List (U8)) xs) (erased (U8) y) (erased (List (U8)) ys)
        (erased (Nat) a) (erased (Dist xs ys a) subst) (erased (Nat) c) (erased (Cost x y c) cost)
        (erased (Nat) s) (erased (Add c a s) ssum)
        (erased (Nat) b) (erased (Dist xs (Cons (U8) y ys) b) delete) (erased (Nat) t) (erased (Add 2 b t) dsum)
        (erased (Nat) e) (erased (Dist (Cons (U8) x xs) ys e) insert) (erased (Nat) u) (erased (Add 2 e u) isum)
        (erased (List (Nat)) ws) (erased (Swap x xs y ys ws) swap)
        (erased (Nat) d) (erased (Least (Cons (Nat) s (Cons (Nat) t (Cons (Nat) u ws))) d) least)
        -> (Dist (Cons (U8) x xs) (Cons (U8) y ys) d)))
  ((Swap : ((U8) x) ((List (U8)) xs) ((U8) y) ((List (U8)) ys) ((List (Nat)) ws) -> Type)
    enum
    (many SwapYes : (erased (U8) x) (erased (U8) y) (erased (List (U8)) xs) (erased (List (U8)) ys)
        (erased (Nat) a) (erased (Dist xs ys a) rest) (erased (Nat) w) (erased (Add 2 a w) sum)
        -> (Swap x (Cons (U8) y xs) y (Cons (U8) x ys) (Cons (Nat) w (Nil (Nat)))))
    (many SwapNoLeft : (erased (U8) x) (erased (U8) y) (erased (List (U8)) ys)
        -> (Swap x (Nil (U8)) y ys (Nil (Nat))))
    (many SwapNoRight : (erased (U8) x) (erased (List (U8)) xs) (erased (U8) y)
        -> (Swap x xs y (Nil (U8)) (Nil (Nat))))
    (many SwapNoFirst : (erased (U8) x) (erased (U8) x2) (erased (List (U8)) xs)
        (erased (U8) y) (erased (U8) y2) (erased (List (U8)) ys) (erased (Apart x y2) apart)
        -> (Swap x (Cons (U8) x2 xs) y (Cons (U8) y2 ys) (Nil (Nat))))
    (many SwapNoSecond : (erased (U8) x) (erased (U8) x2) (erased (List (U8)) xs)
        (erased (U8) y) (erased (U8) y2) (erased (List (U8)) ys) (erased (Apart x2 y) apart)
        -> (Swap x (Cons (U8) x2 xs) y (Cons (U8) y2 ys) (Nil (Nat))))))

; These warnings fire only on code that runs. Erased code (proofs, erased
; arguments and results, the bodies of erased functions) never runs, and thus
; doesn't trigger these warnings: it may match on Nat, apply Succ and call these
; functions freely. A top-level `let` runs when the file is compiled, so it does
; warn.
;! warn Nat at runtime test a number with `u62-lt-dec` or `u62-cmp`, and step it with `u62-dec`
;! warn Succ at runtime use `u62-inc` or `u62-add`
;! warn add use `u62-add`
;! warn nat-add use `u62-add`
;! warn double use `u62-add`
;! warn sub use `u62-sub`
;! warn mul use `u62-mul`
;! warn nat-mul use `u62-mul`
;! warn div use `u62-div`
;! warn divmod use `u62-divmod`
;! warn nat-mod use `u62-mod`
;! warn nat-cmp use `u62-cmp`, or `prove-literal-lt` for a bound between numerals
;! warn lt-dec use `u62-lt-dec`, or `prove-literal-lt` for a bound between numerals
;! warn nat-halve use `u62-shr`
;! warn Half use `u62-shr`
;! warn HZ use `u62-shr`
;! warn H1 use `u62-shr`
;! warn H2 use `u62-shr`
;! warn shl use `u62-shl`
;! warn shr use `u62-shr`
;! warn pow2 use `u62-shl`
;! warn nat-and use `u62-and`
;! warn nat-or use `u62-or`
;! warn nat-xor use `u62-xor`
;! warn array-place use `array-place-imm`
;! warn array-swap use `array-swap-imm`

(def-adts
  ((Text : ((List (U8)) xs) -> Type)
    enum newtype
    (many MkText : (erased (List (U8)) xs) (many (Bytes xs) b) (erased (Nat) n) (erased (Length (U8) xs n) len)
        (erased (Lt n max-array-length) fits) -> (Text xs))))

(def-adts
  ((EditDistance : -> Type)
    enum
    (many MkEditDistance : (erased (Level) L)
        (many (Fn L (erased (List (U8)) xs) (many (Text xs) s) (erased (List (U8)) ys) (many (Text ys) t) ->
            (many (Nat) d) (erased (Dist xs ys d) dist)) f)
        -> (EditDistance))))
(goal many (EditDistance))
