; Lengths of the two strings to compare.
(let ((many perf-n)) 3000)
(let ((many perf-m)) 2800)

(let ((erased (Lt perf-n max-array-length) perf-n-fits)) (prove-literal-lt 3000 18014398509481984))
(let ((erased (Lt perf-m max-array-length) perf-m-fits)) (prove-literal-lt 2800 18014398509481984))
(unary 0)
(let ((erased perf-range-pos)) (prove-literal-lt 0 1073741824))
(let ((erased perf-alphabet-pos)) (prove-literal-lt 0 8))
(let ((erased (Lt 0 u8-modulus) perf-zero-u8)) u8-modulus-pos)

;! suppress warn Nat
;! suppress warn Succ
;! suppress warn nat-add
;! suppress warn nat-mul
;! suppress warn nat-mod
;! suppress warn nat-cmp
;! suppress warn lt-dec
;! suppress warn sub

(let ((erased _) (unique perf-alphabet-u) (erased _)) (str-bytes-copy "abcdABCD"))
(let ((many perf-alphabet)) (share perf-alphabet-u))
(let ((many perf-alphabet-n) (erased perf-alphabet-len)) (bytes-length-many _ perf-alphabet))
(comptime-match many (nat-cmp perf-alphabet-n 8) (CEq _ _ _))

(def-fns _ $ (many perf-fill : (subterm many (Nat) k) (many (Nat) seed) (erased (Nat) n)
    (erased (List (U8)) bs) (unique (Bytes bs) b) (erased (Length (U8) bs n) len) (erased (Lt k (Succ n)) le) ->
    (erased (List (U8)) bs2) (unique (Bytes bs2) b2 at b) (erased (Length (U8) bs2 n) len2))
  (let-match many k (Succ k1) ((Zero) (values bs b len)))
  (let-match erased le (LtS _ _ lt1))
  (let ((many r) (erased _) (erased _)) (nat-mod (nat-add (nat-mul seed 1103515245) 12345) 1073741824 perf-range-pos))
  (let ((many j) (erased j-below) (erased _)) (nat-mod r 8 perf-alphabet-pos))
  (let ((erased _) (erased pick)) (nth-exists _ _ _ _ perf-alphabet-len j-below))
  (let ((many x)) (bytes-get-many _ perf-alphabet j _ pick))
  (let ((erased _) (erased slot)) (nth-exists _ _ _ _ len lt1))
  (let ((erased bs1) (unique b1) (erased set)) (bytes-set _ b k1 x _ slot))
  (tail $ perf-fill k1 r n bs1 b1 (setnth-length _ _ _ _ _ _ set len) (lt-weaken _ _ lt1)))

(def-fns _ $ (many perf-string : (many (Nat) n) (many (Nat) seed) ->
    (erased (List (U8)) bs) (unique (Bytes bs) b) (erased (Length (U8) bs n) len))
  (let ((erased bs0) (unique b0) (erased rep)) (bytes-make n (MkU8 0 perf-zero-u8)))
  (perf-fill n seed n bs0 b0 (repeat-length _ _ _ _ rep) (lt-succ n)))

(def-fns _ $ (many perf-line : (many (String) label) (many (Nat) v) (many (String) rest) -> (many (String) s))
  (str-append label (str-append " " (str-append (nat-str v) (str-append "\n" rest)))))

(def-fns _ $ (many perf-minus : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let-match many (lt-dec b (Succ a)) (Yes _ _ le) ((No _ _ _) 0))
  (let ((many c) (erased _)) (sub a b le))
  c)

(def-lvl Perf)

(def-unique Perf $ (unique perf-start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program Perf) next))
  (let ((erased xs) (unique s0) (erased slen)) (perf-string perf-n 42))
  (let ((erased ys) (unique t0) (erased tlen)) (perf-string perf-m 7))
  (let ((many s)) (MkText xs (share s0) perf-n slen perf-n-fits))
  (let ((many t)) (MkText ys (share t0) perf-m tlen perf-m-fits))
  (let ((unique stop)) (Measure (Stop)))
  (let ((unique w1) (many u0)) (world-do _ w (Measure (Start))))
  (let ((many d) (erased _)) (edit-distance-fast xs s ys t))
  (let ((unique w2) (many u1)) (world-do _ w1 stop))
  (let-match many u0 (MkUsage wall0 user0 sys0 minor0 promoted0 major0 minor-gcs0 major-gcs0))
  (let-match many u1 (MkUsage wall1 user1 sys1 minor1 promoted1 major1 minor-gcs1 major-gcs1))
  (let ((many text))
    (perf-line "distance" d
      $ perf-line "wall-ns" (perf-minus wall1 wall0) $ perf-line "user-ns" (perf-minus user1 user0) $ perf-line "sys-ns" (perf-minus sys1 sys0)
      $ perf-line "minor-words" (perf-minus minor1 minor0) $ perf-line "promoted-words" (perf-minus promoted1 promoted0)
      $ perf-line "major-words" (perf-minus major1 major0)
      $ perf-line "minor-gcs" (perf-minus minor-gcs1 minor-gcs0) $ perf-line "major-gcs" (perf-minus major-gcs1 major-gcs0) ""))
  (let ((unique w3) (many _)) (world-do _ w2 (WriteOut text)))
  (values w3 (Exit Perf (MkU8 0 perf-zero-u8))))

(Continue Perf perf-start)
