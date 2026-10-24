; Certified, allocation-free arithmetic/selection for one non-boundary cell.
; Actual distances are <= 2*(length xs + length ys) < 2^56.  A looser
; uniform 2^60 bound keeps the local arithmetic independent of row indices.
(let ((erased ed-value-limit)) 1152921504606846976)
(unary 1152921504606846977 1152921504606846976)
(unary 1152921504606846978 1152921504606846976)
(let ((erased ed-value-limit-fit)) (prove-literal-lt 1152921504606846976 4611686018427387904))
(let ((erased ed-value-limit1-fit)) (prove-literal-lt 1152921504606846977 4611686018427387904))
(let ((erased ed-value-limit2-fit)) (prove-literal-lt 1152921504606846978 4611686018427387904))

(def-fns _ $ (erased ed-plus1-fit : (erased (Nat) a) (erased (Lt a ed-value-limit) p) ->
    (erased (Lt (Succ a) u62-modulus) q))
  (lt-trans _ _ _ (LtS a ed-value-limit p) ed-value-limit1-fit))

(def-fns _ $ (erased ed-plus2-fit : (erased (Nat) a) (erased (Lt a ed-value-limit) p) ->
    (erased (Lt (Succ (Succ a)) u62-modulus) q))
  (lt-trans _ _ _ (LtS (Succ a) (Succ ed-value-limit) (LtS a ed-value-limit p)) ed-value-limit2-fit))

(def-fns _ $ (many ed-plus2 : (many (Nat) a) (erased (Lt a ed-value-limit) pa) ->
    (many (Nat) b) (erased (Add 2 a b) sum) (erased (Lt b u62-modulus) pb))
  (let ((erased sum)) (AddSucc 1 a (Succ a) (AddSucc 0 a a (AddZero a))))
  (let ((erased pb)) (ed-plus2-fit a pa))
  (values (u62-add 2 a (Succ (Succ a)) sum pb) sum pb))

(def-fns _ $ (erased ed-cost-sum-fit : (erased (U8) x y) (erased (Nat) c)
    (erased (Cost x y c) cost) (erased (Nat) a) (erased (Lt a ed-value-limit) pa)
    (erased (Nat) s) (erased (Add c a s) sum) -> (erased (Lt s u62-modulus) ps))
  (match erased cost _
    ((CostSame _)
      (let-match erased sum (AddZero _))
      (lt-trans a ed-value-limit u62-modulus pa ed-value-limit-fit))
    ((CostCase _ _ _ _ _ _)
      (let-match erased sum (AddSucc _ _ _ sum1))
      (let-match erased sum1 (AddZero _))
      (ed-plus1-fit a pa))
    ((CostOther _ _ _ _ _ _ _)
      (let-match erased sum (AddSucc _ _ _ sum1))
      (let-match erased sum1 (AddSucc _ _ _ sum2))
      (let-match erased sum2 (AddZero _))
      (ed-plus2-fit a pa))))

(def-fns _ $ (many ed-subst-sum : (many (U8) x y) (many (Nat) a) (erased (Lt a ed-value-limit) pa) ->
    (erased (Nat) c) (erased (Cost x y c) cost) (many (Nat) s) (erased (Add c a s) sum) (erased (Lt s u62-modulus) ps))
  (let ((many c) (erased cost)) (ed-cost x y))
  (let ((erased s) (erased sum)) (add c a))
  (let ((erased ps)) (ed-cost-sum-fit x y c cost a pa s sum))
  (values c cost (u62-add c a s sum ps) sum ps))

; Three ordinary candidates. The caller certifies the absence of a swap.
(def-fns _ $ (many ed-step3 : (many (U8) x) (erased (List (U8)) xs) (many (U8) y) (erased (List (U8)) ys)
    (many (Nat) a) (erased (Dist xs ys a) da) (erased (Lt a ed-value-limit) pa)
    (many (Nat) b) (erased (Dist xs (Cons (U8) y ys) b) db) (erased (Lt b ed-value-limit) pb)
    (many (Nat) e) (erased (Dist (Cons (U8) x xs) ys e) de) (erased (Lt e ed-value-limit) pe)
    (erased (Swap x xs y ys (Nil (Nat))) swap) ->
    (many (Nat) d) (erased (Dist (Cons (U8) x xs) (Cons (U8) y ys) d) dist) (erased (Lt d u62-modulus) pd))
  (let ((erased c) (erased cost) (many s) (erased sa) (erased ps)) (ed-subst-sum x y a pa))
  (let ((many t) (erased tb) (erased pt)) (ed-plus2 b pb))
  (let ((many u) (erased ue) (erased pu)) (ed-plus2 e pe))
  (let ((many d) (erased least) (erased pd)) (ed-min3 s t u ps pt pu))
  (values d (DistStep x xs y ys a da c cost s sa b db t tb e de u ue (Nil _) swap d least) pd))

; Four candidates. The caller has already read the i+2,j+2 cell, tested the
; crossed bytes, and formed its +2 swap candidate, so there is no live Option.
(def-fns _ $ (many ed-step4 : (many (U8) x) (erased (List (U8)) xs) (many (U8) y) (erased (List (U8)) ys)
    (many (Nat) a) (erased (Dist xs ys a) da) (erased (Lt a ed-value-limit) pa)
    (many (Nat) b) (erased (Dist xs (Cons (U8) y ys) b) db) (erased (Lt b ed-value-limit) pb)
    (many (Nat) e) (erased (Dist (Cons (U8) x xs) ys e) de) (erased (Lt e ed-value-limit) pe)
    (many (Nat) w) (erased (Lt w u62-modulus) pw) (erased (Swap x xs y ys (Cons (Nat) w (Nil (Nat)))) swap) ->
    (many (Nat) d) (erased (Dist (Cons (U8) x xs) (Cons (U8) y ys) d) dist) (erased (Lt d u62-modulus) pd))
  (let ((erased c) (erased cost) (many s) (erased sa) (erased ps)) (ed-subst-sum x y a pa))
  (let ((many t) (erased tb) (erased pt)) (ed-plus2 b pb))
  (let ((many u) (erased ue) (erased pu)) (ed-plus2 e pe))
  (let ((many d) (erased least) (erased pd)) (ed-min4 s t u w ps pt pu pw))
  (values d (DistStep x xs y ys a da c cost s sa b db t tb e de u ue (Cons _ w (Nil _)) swap d least) pd))
