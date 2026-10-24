; Cached lookahead bytes and flags are immediate. Their logical histories
; are erased, so deciding a swap never allocates an Option or a list.
(def-adts $ (EdHead : ((List (U8)) rest) ((U8) byte) ((Bool) present) -> Type)
  enum
  (many EdHeadNil : (erased (U8) byte) -> (EdHead (Nil (U8)) byte (BFalse)))
  (many EdHeadCons : (erased (U8) byte) (erased (List (U8)) rest) ->
    (EdHead (Cons (U8) byte rest) byte (BTrue))))

(def-adts $ (EdPrevious : ((List (U8)) xs) ((List (U8)) ys)
    ((List (Copy (U62))) cells) ((U8) byte) ((Bool) present) -> Type)
  enum
  (many EdPreviousNil : (erased (List (U8)) ys) (erased (List (Copy (U62))) cells) (erased (U8) byte) ->
    (EdPrevious (Nil (U8)) ys cells byte (BFalse)))
  (many EdPreviousCons : (erased (U8) byte) (erased (List (U8)) xs ys)
    (erased (List (Copy (U62))) cells) (erased (EdRow xs ys cells) row) ->
    (EdPrevious (Cons (U8) byte xs) ys cells byte (BTrue))))

; Select a cell, borrowing the previous-previous row only if the crossed
; bytes agree. i is the column of rest; the new cell is at i-1.
(def-fns _ $ (many ed-select-cell :
    (many (U8) x) (erased (List (U8)) xs) (many (U8) y) (erased (List (U8)) rest)
    (erased (List (U8)) ys) (erased (Nat) n) (erased (Length (U8) ys n) len) (erased (Lt n max-array-length) fits)
    (many (Nat) i) (erased (EdSuffix (U8) ys i rest) suffix)
    (many (U8) x2) (many (Bool) has-x) (erased (List (Copy (U62))) old)
    (erased (EdPrevious xs ys old x2 has-x) previous) (unique (Array (Copy (U62)) old) prev2)
    (many (U8) y2) (many (Bool) has-y) (erased (EdHead rest y2 has-y) head)
    (many (Nat) a) (erased (Dist xs rest a) da) (erased (Lt a ed-value-limit) pa)
    (many (Nat) b) (erased (Dist xs (Cons (U8) y rest) b) db) (erased (Lt b ed-value-limit) pb)
    (many (Nat) e) (erased (Dist (Cons (U8) x xs) rest e) de) (erased (Lt e ed-value-limit) pe) ->
    (many (Nat) d) (erased (Dist (Cons (U8) x xs) (Cons (U8) y rest) d) dist)
    (erased (Lt d u62-modulus) pd) (unique prev2 is out at prev2))
  (let-match many has-x (BTrue)
    ((BFalse)
      (let-match erased previous (EdPreviousNil _ _ _))
      (let ((many d) (erased dist) (erased pd))
        (ed-step3 x (Nil _) y rest a da pa b db pb e de pe (SwapNoLeft x y rest)))
      (values d dist pd prev2)))
  (let-match erased previous (EdPreviousCons _ xs2 _ _ row2))
  (let-match many has-y (BTrue)
    ((BFalse)
      (let-match erased head (EdHeadNil _))
      (let ((many d) (erased dist) (erased pd))
        (ed-step3 x xs y (Nil _) a da pa b db pb e de pe (SwapNoRight x xs y)))
      (values d dist pd prev2)))
  (let-match erased head (EdHeadCons _ ys2))
  (let-match many (ed-byte-eq x y2) (Equal _ _ _)
    ((Unequal _ _ _ _ apart)
      (let ((many d) (erased dist) (erased pd))
        (ed-step3 x xs y rest a da pa b db pb e de pe (SwapNoFirst x x2 xs2 y y2 ys2 apart)))
      (values d dist pd prev2)))
  (let-match many (ed-byte-eq x2 y) (Equal _ _ _)
    ((Unequal _ _ _ _ apart)
      (let ((many d) (erased dist) (erased pd))
        (ed-step3 x xs y rest a da pa b db pb e de pe (SwapNoSecond x x2 xs2 y y2 ys2 apart)))
      (values d dist pd prev2)))
  (let ((erased inside)) (nth-lt-length (U8) ys i n x (ed-suffix-nth (U8) ys i x ys2 suffix) len))
  (let ((many next)) (u62-inc i (ed-succ-length-fit i (lt-trans i n max-array-length inside fits))))
  (let ((many v) (erased dv) (erased pv) (unique prev2a))
    (ed-row-get xs2 ys old row2 prev2 next ys2 (ed-suffix-next (U8) ys i x ys2 suffix)))
  (let ((many w) (erased sum) (erased pw)) (ed-plus2 v pv))
  (let ((many d) (erased dist) (erased pd))
    (ed-step4 x xs y rest a da pa b db pb e de pe w pw (SwapYes x y xs2 ys2 v dv w sum)))
  (values d dist pd prev2a))
