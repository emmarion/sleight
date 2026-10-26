; Standalone regression/space test; compile after the library files, without
; edit-distance-fast/perf.sl. Expected sum=130508, singleton=1, swap=2.
; The two minor-word counters should differ by only a constant (Measure).
(let ((erased ed-test-zero-small)) (prove-literal-lt 0 1152921504606846976))
(let ((erased ed-test-two-small)) (prove-literal-lt 2 1152921504606846976))
(let ((erased ed-test-four-small)) (prove-literal-lt 4 1152921504606846976))
(let ((erased ed-test-one-length)) (prove-literal-lt 1 18014398509481984))
(let ((erased ed-test-two-length)) (prove-literal-lt 2 18014398509481984))
(let ((erased (Add 2 0 2) ed-test-add20)) (AddSucc 1 0 1 (AddSucc 0 0 0 (AddZero 0))))
(unary 4)
(let ((erased (Add 2 2 4) ed-test-add22)) (AddSucc _ _ _ (AddSucc _ _ _ (AddZero 2))))

(def-fns _ $ (many ed-test-single : (many (U8) x y) -> (many (Nat) d)
    (erased (Dist (Cons (U8) x (Nil (U8))) (Cons (U8) y (Nil (U8))) d) dist)
    (erased (Lt d ed-value-limit) small))
  (let ((many d) (erased dist) (erased _))
    (ed-step3 x (Nil _) y (Nil _)
      0 (DistNil) ed-test-zero-small
      2 (DistInsert y (Nil _) 0 (DistNil) 2 ed-test-add20) ed-test-two-small
      2 (DistDelete x (Nil _) 0 (DistNil) 2 ed-test-add20) ed-test-two-small
      (SwapNoLeft x y (Nil _))))
  (values d dist (ed-dist-small _ _ d dist 1 1
    (LengthCons _ x (Nil _) 0 (LengthNil _)) (LengthCons _ y (Nil _) 0 (LengthNil _))
    ed-test-one-length ed-test-one-length)))

(def-fns _ $ (many ed-test-swap : (many (U8) x y) -> (many (Nat) d))
  (let ((erased xx)) (Cons (U8) x (Nil (U8))))
  (let ((erased yy)) (Cons (U8) y (Nil (U8))))
  (let ((erased ix)) (DistInsert x (Nil _) 0 (DistNil) 2 ed-test-add20))
  (let ((erased dy)) (DistDelete y (Nil _) 0 (DistNil) 2 ed-test-add20))
  (let ((many a) (erased da) (erased pa)) (ed-test-single y x))
  (let ((many b) (erased db) (erased _))
    (ed-step3 y (Nil _) y xx
      2 ix ed-test-two-small
      4 (DistInsert y xx 2 ix 4 ed-test-add22) ed-test-four-small
      a da pa (SwapNoLeft y y xx)))
  (let ((many e) (erased de) (erased _))
    (ed-step3 x yy x (Nil _)
      2 dy ed-test-two-small a da pa
      4 (DistDelete x yy 2 dy 4 ed-test-add22) ed-test-four-small
      (SwapNoRight x yy x)))
  (let ((erased lx)) (LengthCons (U8) x (Nil _) 0 (LengthNil _)))
  (let ((erased ly)) (LengthCons (U8) y (Nil _) 0 (LengthNil _)))
  (let ((erased pb)) (ed-dist-small yy (Cons _ y xx) b db 1 2 ly (LengthCons _ y xx 1 lx) ed-test-one-length ed-test-two-length))
  (let ((erased pe)) (ed-dist-small (Cons _ x yy) xx e de 2 1 (LengthCons _ x yy 1 ly) lx ed-test-two-length ed-test-one-length))
  (let ((many d) (erased _) (erased _))
    (ed-step4 x yy y xx a da pa b db pb e de pe
      2 (prove-literal-lt 2 4611686018427387904)
      (SwapYes x y (Nil _) (Nil _) 0 (DistNil) 2 ed-test-add20)))
  d)

(def-fns _ $ (many ed-test-inner : (many (U8) x) (subterm many (Nat) n) (erased (Lt n (Succ u8-modulus)) pn)
    (many (Nat) s) (erased (Lt s u62-modulus) ps) -> (many (Nat) total) (erased (Lt total u62-modulus) pt))
  (let ((erased nf)) (lt-le-trans _ _ _ pn (LtS _ _ u8-below-u62)))
  (let-match many (u62-lt-dec 0 n u62-modulus-pos nf) (Yes _ _ pos) ((No _ _ _) (values s ps)))
  (let-match erased pos (LtZ k))
  (let-match erased pn (LtS _ _ pk))
  (let ((many j)) (u62-dec k n nf))
  (let-match many (u62-lt-dec s 1152921504606846976 ps ed-value-limit-fit) (Yes _ _ small)
    ((No _ _ _) (values s ps)))
  (let ((erased _) (erased _) (many t) (erased _) (erased pt)) (ed-subst-sum x (MkU8 j pk) s small))
  (tail (ed-test-inner x j (lt-weaken _ _ pk) t pt)))

(def-fns _ $ (many ed-test-outer : (subterm many (Nat) n) (erased (Lt n (Succ u8-modulus)) pn)
    (many (Nat) s) (erased (Lt s u62-modulus) ps) -> (many (Nat) total))
  (let ((erased nf)) (lt-le-trans _ _ _ pn (LtS _ _ u8-below-u62)))
  (let-match many (u62-lt-dec 0 n u62-modulus-pos nf) (Yes _ _ pos) ((No _ _ _) s))
  (let-match erased pos (LtZ k))
  (let-match erased pn (LtS _ _ pk))
  (let ((many j)) (u62-dec k n nf))
  (let ((many t) (erased pt)) (ed-test-inner (MkU8 j pk) u8-modulus (lt-succ u8-modulus) s ps))
  (tail (ed-test-outer j (lt-weaken _ _ pk) t pt)))

(def-fns _ $ (many ed-test-initial-row : (many (Nat) n) (erased (Lt n max-array-length) fits) -> (many (Nat) d))
  (let ((erased ys) (erased rep)) (repeat-exists (U8) n (MkU8 0 u8-modulus-pos)))
  (let ((erased cells) (unique a) (erased row)) (ed-initial-row ys n (repeat-length _ _ _ _ rep) fits))
  (let ((many d) (erased _) (erased _) (unique _)) (ed-row-get (Nil _) ys cells row a 0 ys (EdSuffixHere (U8) ys)))
  d)

; A real Text checks the byte-access and boundary wrappers as well.
(let ((erased ed-test-bytes-xs) (unique ed-test-bytes-u) (erased _)) (str-bytes-copy "abc"))
(let ((many ed-test-bytes)) (share ed-test-bytes-u))
(let ((many ed-test-bytes-n) (erased ed-test-bytes-len)) (bytes-length-many _ ed-test-bytes))
(unary ed-test-bytes-n)
(unary 3)
(let ((many ed-test-text)) (MkText ed-test-bytes-xs ed-test-bytes ed-test-bytes-n ed-test-bytes-len (prove-literal-lt 3 18014398509481984)))

(def-fns _ $ (many ed-test-last-byte : -> (many (Nat) code))
  (let ((erased suffix)) (ed-suffix-end (U8) ed-test-bytes-xs 3 ed-test-bytes-len))
  (let ((erased x) (erased prev)) (ed-suffix-prev (U8) ed-test-bytes-xs 2 (Nil _) suffix))
  (let ((many byte)) (bytes-get-many ed-test-bytes-xs ed-test-bytes 2 x (ed-suffix-nth (U8) ed-test-bytes-xs 2 x (Nil _) prev)))
  (let-match many byte (MkU8 code _))
  code)

(def-fns _ $ (many ed-test-line : (many (String) label) (many (Nat) n) (many (String) rest) -> (many (String) s))
  (str-append label (str-append " " (str-append (nat-str n) (str-append "\n" rest)))))

(def-lvl EdTest)
(def-unique EdTest $ (unique ed-test-start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program EdTest) next))
  (let ((unique stop)) (Measure (Stop)))
  (let ((unique w1) (many before)) (world-do _ w (Measure (Start))))
  (let ((many sum)) (ed-test-outer u8-modulus (lt-succ u8-modulus) 0 u62-modulus-pos))
  (let ((many one) (erased _) (erased _)) (ed-test-single (MkU8 97 (prove-literal-lt 97 u8-modulus)) (MkU8 65 (prove-literal-lt 65 u8-modulus))))
  (let ((many sw)) (ed-test-swap (MkU8 97 (prove-literal-lt 97 u8-modulus)) (MkU8 98 (prove-literal-lt 98 u8-modulus))))
  (let ((many row-head)) (ed-test-initial-row 20000 (prove-literal-lt 20000 18014398509481984)))
  (let ((many empty-row)) (ed-test-initial-row 0 (prove-literal-lt 0 18014398509481984)))
  (let ((many largest) (erased _) (erased _)) (ed-double-length 18014398509481983 (prove-literal-lt 18014398509481983 18014398509481984)))
  (let ((many boundary-left) (erased _) (erased _)) (ed-boundary-left ed-test-bytes-xs ed-test-text))
  (let ((many boundary-right) (erased _) (erased _)) (ed-boundary-right ed-test-bytes-xs ed-test-text))
  (let ((many last-byte)) (ed-test-last-byte))
  (let ((unique w2) (many after)) (world-do _ w1 stop))
  (let-match many before (MkUsage _ _ _ minor0 _ major0 _ _))
  (let-match many after (MkUsage _ _ _ minor1 _ major1 _ _))
  (let ((many text))
    (ed-test-line "all-byte-cost-sum" sum $ ed-test-line "singleton" one $ ed-test-line "swap" sw
      $ ed-test-line "initial-row-head" row-head $ ed-test-line "empty-row-head" empty-row $ ed-test-line "largest-boundary" largest
      $ ed-test-line "boundary-left" boundary-left $ ed-test-line "boundary-right" boundary-right $ ed-test-line "last-byte" last-byte
      $ ed-test-line "minor-before" minor0 $ ed-test-line "minor-after" minor1
      $ ed-test-line "major-before" major0 $ ed-test-line "major-after" major1 ""))
  (let ((unique w3) (many _)) (world-do _ w2 (WriteOut text)))
  (values w3 (Exit EdTest (MkU8 0 u8-modulus-pos))))
(Continue EdTest ed-test-start)
