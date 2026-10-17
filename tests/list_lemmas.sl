; needs: ../std/list
; expect: "ok"
(def-fns _ $ (erased length-again : (erased Type A) (erased (List A) xs) (erased (Nat) n) (erased (Length A xs n) len) ->
    (erased (Eq (Nat) n n) e))
  (let ((erased _) (erased len2)) (length-exists _ xs))
  (let-match erased (length-fn _ _ _ _ len len2) (Refl _ _))
  (Refl _ n))

(def-fns _ $ (erased read-back : (erased Type A) (erased (List A) xs) (erased (Nat) i n) (erased A y) (erased (List A) ys)
    (erased (SetNth A xs i y ys) p) (erased (Length A xs n) len) -> (erased (Nth A ys i y) q) (erased (Lt i n) lt))
  (let ((erased q)) (setnth-nth _ _ _ _ _ p))
  (values q (nth-lt-length _ _ _ _ _ q (setnth-length _ _ _ _ _ _ p len))))

(def-fns _ $ (erased found : (erased Type A) (erased (List A) xs) (erased (Nat) i n) (erased A x)
    (erased (Length A xs n) len) (erased (Nth A xs i x) q) -> (erased (Eq A x x) e))
  (let ((erased _) (erased q2)) (nth-exists _ _ _ i len (nth-lt-length _ _ _ _ _ q len)))
  (let-match erased (nth-fn _ _ _ _ _ q q2) (Refl _ _))
  (Refl _ x))

(def-fns _ $ (erased written : (erased Type A) (erased (List A) xs ys) (erased (Nat) i n) (erased A y)
    (erased (Length A xs n) len) (erased (Lt i n) lt) (erased (SetNth A xs i y ys) p) -> (erased (Eq (List A) ys ys) e))
  (let ((erased _) (erased p2)) (setnth-exists _ _ _ _ y len lt))
  (let-match erased (setnth-fn _ _ _ _ _ _ p p2) (Refl _ _))
  (Refl _ ys))

(def-fns _ $ (erased others : (erased Type A) (erased (List A) xs) (erased (Nat) i j k) (erased A y x w) (erased (List A) ys)
    (erased (SetNth A xs i y ys) p) (erased (Nth A xs j x) q) (erased (Lt j i) lt) (erased (Nth A xs k w) r) (erased (Lt i k) gt) ->
    (erased (Nth A xs j x) q2) (erased (Nth A xs k w) r2))
  (values
    (setnth-back-lt _ _ _ _ _ _ _ p (setnth-nth-lt _ _ _ _ _ _ _ p q lt) lt)
    (setnth-back-gt _ _ _ _ _ _ _ p (setnth-nth-gt _ _ _ _ _ _ _ p r gt) gt)))

(def-fns _ $ (erased rewrites : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i) (erased A x y)
    (erased (Nth A xs i x) q) (erased (SetNth A xs i y ys) p) (erased (SetNth A ys i x zs) p2) -> (erased (Eq (List A) xs zs) e))
  (setnth-same _ _ _ _ _ q (setnth-twice _ _ _ _ _ _ _ p p2)))

(def-fns _ $ (erased reorder : (erased Type A) (erased (List A) xs ys zs) (erased (Nat) i j) (erased A y z)
    (erased (SetNth A xs i y ys) p) (erased (SetNth A ys j z zs) q) (erased (Lt i j) lt) ->
    (erased (List A) vs) (erased (SetNth A xs i y vs) r) (erased (SetNth A vs j z zs) s))
  (let ((erased _) (erased r1) (erased s1)) (setnth-commute-lt _ _ _ _ _ _ _ _ p q lt))
  (setnth-commute-gt _ _ _ _ _ _ _ _ r1 s1 lt))

(def-fns _ $ (erased filled : (erased Type A) (erased (Nat) n i) (erased A x y) (erased (List A) xs)
    (erased (Repeat A n x xs) p) (erased (Lt i n) lt) (erased (Nth A xs i y) q) ->
    (erased (Length A xs n) len) (erased (Nth A xs i x) r) (erased (Eq A x y) e))
  (values (repeat-length _ _ _ _ p) (repeat-nth _ _ _ _ _ p lt) (repeat-elem _ _ _ _ _ _ p q)))

(def-fns _ $ (erased filled-once : (erased Type A) (erased (Nat) n) (erased A x) (erased (List A) xs)
    (erased (Repeat A n x xs) p) -> (erased (Eq (List A) xs xs) e))
  (let ((erased _) (erased p2)) (repeat-exists _ n x))
  (let-match erased (repeat-fn _ _ _ _ _ p p2) (Refl _ _))
  (Refl _ xs))

"ok"
