; Both empty-string cases can be computed without a loop or allocation.
(def-fns _ $ (erased ed-empty-left : (erased (List (U8)) ys) (erased (Nat) n d)
    (subterm erased (Length (U8) ys n) len) (erased (Double n d) twice) -> (erased (Dist (Nil (U8)) ys d) dist))
  (let-match erased len (LengthCons _ y rest n1 len1)
    ((LengthNil _) (let-match erased twice (D0)) (DistNil)))
  (let-match erased twice (DS _ d1 twice1))
  (DistInsert y rest d1 (ed-empty-left rest n1 d1 len1 twice1) d
    (AddSucc 1 d1 (Succ d1) (AddSucc 0 d1 d1 (AddZero d1)))))

(def-fns _ $ (erased ed-empty-right : (erased (List (U8)) xs) (erased (Nat) n d)
    (subterm erased (Length (U8) xs n) len) (erased (Double n d) twice) -> (erased (Dist xs (Nil (U8)) d) dist))
  (let-match erased len (LengthCons _ x rest n1 len1)
    ((LengthNil _) (let-match erased twice (D0)) (DistNil)))
  (let-match erased twice (DS _ d1 twice1))
  (DistDelete x rest d1 (ed-empty-right rest n1 d1 len1 twice1) d
    (AddSucc 1 d1 (Succ d1) (AddSucc 0 d1 d1 (AddZero d1)))))

(def-fns _ $ (many ed-double-length : (many (Nat) n) (erased (Lt n max-array-length) fits) ->
    (many (Nat) d) (erased (Double n d) twice) (erased (Lt d ed-value-limit) small))
  (let ((erased d) (erased twice)) (double n))
  (let ((erased pd)) (double-mono n max-array-length d 36028797018963968 fits twice ed-max-double))
  (let ((erased small)) (lt-trans _ _ _ pd (prove-literal-lt 36028797018963968 1152921504606846976)))
  (values (u62-add n n d (ed-double-add n d twice) (lt-trans d ed-value-limit u62-modulus small ed-value-limit-fit)) twice small))

(def-fns _ $ (many ed-boundary-left : (erased (List (U8)) ys) (many (Text ys) text) ->
    (many (Nat) d) (erased (Dist (Nil (U8)) ys d) dist) (erased (Lt d ed-value-limit) small))
  (let ((many n) (erased len) (erased fits) (erased _)) (ed-text-length ys text))
  (let ((many d) (erased twice) (erased small)) (ed-double-length n fits))
  (values d (ed-empty-left ys n d len twice) small))

(def-fns _ $ (many ed-boundary-right : (erased (List (U8)) xs) (many (Text xs) text) ->
    (many (Nat) d) (erased (Dist xs (Nil (U8)) d) dist) (erased (Lt d ed-value-limit) small))
  (let ((many n) (erased len) (erased fits) (erased _)) (ed-text-length xs text))
  (let ((many d) (erased twice) (erased small)) (ed-double-length n fits))
  (values d (ed-empty-right xs n d len twice) small))
