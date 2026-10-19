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
  ((AllTo : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) (A m) -> Type)
    enum
    (many AllToNil : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A m)
        -> (AllTo A R (Nil A) m))
    (many AllToCons : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A x)
        (erased (List A) xs) (erased A m) (erased (R x m) p) (erased (AllTo A R xs m) rest)
        -> (AllTo A R (Cons A x xs) m))))

(def-adts
  ((Ascending : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) -> Type)
    enum
    (many AscNil : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) -> (Ascending A R (Nil A)))
    (many AscOne : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A x)
        -> (Ascending A R (Cons A x (Nil A))))
    (many AscCons : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A x) (erased A y)
        (erased (List A) rest) (erased (R x y) le) (erased (Ascending A R (Cons A y rest)) a)
        -> (Ascending A R (Cons A x (Cons A y rest))))))

(def-adts
  ((Permutation : (Type A) ((List A) xs) ((List A) ys) -> Type)
    enum
    (many PNil : (erased Type A) -> (Permutation A (Nil A) (Nil A)))
    (many PSkip : (erased Type A) (erased A x) (erased (List A) xs) (erased (List A) ys)
        (erased (Permutation A xs ys) p)
        -> (Permutation A (Cons A x xs) (Cons A x ys)))
    (many PSwap : (erased Type A) (erased A x) (erased A y) (erased (List A) l)
        -> (Permutation A (Cons A x (Cons A y l)) (Cons A y (Cons A x l))))
    (many PTrans : (erased Type A) (erased (List A) xs) (erased (List A) ys) (erased (List A) zs)
        (erased (Permutation A xs ys) p) (erased (Permutation A ys zs) q)
        -> (Permutation A xs zs))))

(def-adts
  ((SortedPerm : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) ((List A) ys) -> Type)
    enum
    (many MkSortedPerm : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R)
        (erased (List A) xs) (erased (List A) ys)
        (erased (Ascending A R ys) sorted) (erased (Permutation A xs ys) perm)
        -> (SortedPerm A R xs ys))))

(def-adts
  ((Copies : (Type A) ((List A) xs) ((List (Copy A)) cs) -> Type)
    enum
    (many CopiesNil : (erased Type A) -> (Copies A (Nil A) (Nil (Copy A))))
    (many CopiesCons : (erased Type A) (erased A x) (erased (List A) xs) (erased (List (Copy A)) cs)
        (erased (Copies A xs cs) rest) -> (Copies A (Cons A x xs) (Cons (Copy A) (MkCopy A x) cs)))))

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
  ((Heapsort : -> Type)
    enum
    (many MkHeapsort : (erased (Level) L)
        (many (Fn L (erased (List (Nat)) xs) (erased (AllTo (Nat) Lt xs u62-modulus) small)
            (erased (Nat) n) (erased (Length (Nat) xs n) len) (erased (Lt n max-array-length) fits)
            (erased (List (Copy (Nat))) cs) (unique (Array (Copy (Nat)) cs) a) (erased (Copies (Nat) xs cs) rel) ->
            (erased (List (Nat)) ys) (erased (List (Copy (Nat))) ds) (unique (Array (Copy (Nat)) ds) r at a)
            (erased (Copies (Nat) ys ds) rel2) (erased (SortedPerm (Nat) Le xs ys) correct)) f)
        -> (Heapsort))))
(goal many (Heapsort))
