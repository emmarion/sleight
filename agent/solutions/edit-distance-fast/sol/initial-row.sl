; A first complete array loop: the row Dist [] (suffix ys) is 2*its length.
; It writes from right to left, never reads target bytes at runtime, and
; allocates exactly one array. The same partial-row invariant can be used
; for each subsequent source byte.
(def-fns _ $ (erased ed-suffix-small-length : (erased (List (U8)) ys) (erased (Nat) n)
    (erased (Length (U8) ys n) len) (erased (Lt n max-array-length) fits)
    (erased (Nat) i) (erased (List (U8)) rest) (erased (EdSuffix (U8) ys i rest) suffix) ->
    (erased (Nat) m) (erased (Length (U8) rest m) lr) (erased (Lt m max-array-length) small))
  (let ((erased m) (erased lr) (erased sum)) (ed-suffix-length (U8) ys i rest suffix n len))
  (values m lr (lt-le-trans m (Succ n) max-array-length (add-le-right i m n sum) (LtS n max-array-length fits))))

(def-fns _ $ (erased ed-succ-length-fit : (erased (Nat) n) (erased (Lt n max-array-length) fits) ->
    (erased (Lt (Succ n) u62-modulus) p))
  (lt-le-trans (Succ n) (Succ max-array-length) u62-modulus
    (LtS n max-array-length fits) (LtS max-array-length u62-modulus max-array-length-below-u62)))

(def-fns _ $ (many ed-initial-row-loop : (erased (List (U8)) ys) (erased (Nat) n)
    (erased (Length (U8) ys n) len) (erased (Lt n max-array-length) fits)
    (subterm many (Nat) i) (erased (Lt i (Succ n)) in)
    (erased (List (U8)) rest) (erased (EdSuffix (U8) ys i rest) suffix)
    (erased (List (Copy (U62))) cells) (unique (Array (Copy (U62)) cells) a)
    (erased (List (Copy (U62))) partial) (erased (EdSuffix (Copy (U62)) cells i partial) computed)
    (erased (EdRow (Nil (U8)) rest partial) row)
    (many (Nat) d) (erased (Dist (Nil (U8)) rest d) dist) (erased (Lt d ed-value-limit) small) ->
    (erased (List (Copy (U62))) updated) (unique (Array (Copy (U62)) updated) out at a)
    (erased (EdRow (Nil (U8)) ys updated) final-row))
  (let ((erased ip)) (lt-le-trans i (Succ n) u62-modulus in
    (LtS n u62-modulus (lt-trans n max-array-length u62-modulus fits max-array-length-below-u62))))
  (let-match many (u62-lt-dec 0 i u62-modulus-pos ip) (Yes _ _ pos)
    ((No _ _ iz)
      (let-match erased iz (LtZ _) (absurd (LtS _ _ bad) bad))
      (let-match erased suffix (EdSuffixHere _ _))
      (let-match erased computed (EdSuffixHere _ _))
      (values cells a row)))
  (let-match erased pos (LtZ k))
  (let ((many j)) (u62-dec k i ip))
  (let ((erased y) (erased prev)) (ed-suffix-prev (U8) ys k rest suffix))
  (let ((many e) (erased sum) (erased pe)) (ed-plus2 d small))
  (let ((erased de)) (DistInsert y rest d dist e sum))
  (let ((erased m) (erased lm) (erased pm)) (ed-suffix-small-length ys n len fits k (Cons _ y rest) prev))
  (let ((erased se)) (ed-dist-small (Nil _) (Cons _ y rest) e de 0 m (LengthNil _) lm
    (prove-literal-lt 0 18014398509481984) pm))
  (let ((erased updated) (unique out) (erased new-computed)) (ed-array-before cells a j partial computed e pe))
  (let ((erased new-row)) (EdRowCons (Nil _) y rest e pe de se partial row))
  (let-match erased in (LtS _ _ kn))
  (tail (ed-initial-row-loop ys n len fits j (lt-weaken k n kn) (Cons _ y rest) prev updated out
    (Cons _ (MkCopy _ (MkU62 e pe)) partial) new-computed new-row e de se)))

(def-fns _ $ (many ed-initial-row : (erased (List (U8)) ys) (many (Nat) n)
    (erased (Length (U8) ys n) len) (erased (Lt n max-array-length) fits) ->
    (erased (List (Copy (U62))) cells) (unique (Array (Copy (U62)) cells) out)
    (erased (EdRow (Nil (U8)) ys cells) row))
  (let ((many count)) (u62-inc n (ed-succ-length-fit n fits)))
  (let ((erased cells0) (unique a0) (erased rep)) (array-make (U62) count (MkU62 0 u62-modulus-pos)))
  (let ((erased last)) (ed-suffix-end (Copy (U62)) cells0 (Succ n) (repeat-length _ _ _ _ rep)))
  (let ((erased cells1) (unique a1) (erased computed)) (ed-array-before cells0 a0 n (Nil _) last 0 u62-modulus-pos))
  (ed-initial-row-loop ys n len fits n (lt-succ n) (Nil _) (ed-suffix-end (U8) ys n len) cells1 a1
    (Cons _ (MkCopy _ (MkU62 0 u62-modulus-pos)) (Nil _)) computed
    (EdRowNil (Nil _) 0 u62-modulus-pos (DistNil) (prove-literal-lt 0 1152921504606846976))
    0 (DistNil) (prove-literal-lt 0 1152921504606846976)))
