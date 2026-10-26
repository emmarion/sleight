(unary 0)
(let ((erased perf-range-pos)) (prove-literal-lt 0 1073741824))
(let ((erased perf-low-pos)) (prove-literal-lt 0 1024))
(let ((erased perf-high-pos)) (prove-literal-lt 0 1048576))
(let ((erased perf-period-pos)) (prove-literal-lt 0 331))
(let ((erased (Lt 0 u8-modulus) perf-zero-u8)) u8-modulus-pos)

;! suppress warn Nat
;! suppress warn Succ
;! suppress warn nat-add
;! suppress warn nat-mul
;! suppress warn nat-mod
;! suppress warn nat-cmp
;! suppress warn lt-dec
;! suppress warn sub
;! suppress warn div

(def-adts $ (PerfAlphabet : -> Type)
  enum
  (many MkPerfAlphabet : (erased (List (U8)) cs) (many (Bytes cs) b) (many (Nat) n) (erased (Length (U8) cs n) len)
     (erased (Lt (Zero) n) pos) -> (PerfAlphabet)))

(let ((erased _) (unique perf-letters-u) (erased _)) (str-bytes-copy "abcdABCD"))
(let ((many perf-letters-b)) (share perf-letters-u))
(let ((many perf-letters-n) (erased perf-letters-len)) (bytes-length-many _ perf-letters-b))
(comptime-match many (nat-cmp perf-letters-n 8) (CEq _ _ _))
(let ((many perf-letters)) (MkPerfAlphabet _ perf-letters-b perf-letters-n perf-letters-len (prove-literal-lt 0 8)))

(let ((erased _) (unique perf-cases-u) (erased _)) (str-bytes-copy "aA"))
(let ((many perf-cases-b)) (share perf-cases-u))
(let ((many perf-cases-n) (erased perf-cases-len)) (bytes-length-many _ perf-cases-b))
(comptime-match many (nat-cmp perf-cases-n 2) (CEq _ _ _))
(let ((many perf-cases)) (MkPerfAlphabet _ perf-cases-b perf-cases-n perf-cases-len (prove-literal-lt 0 2)))

(def-fns _ $ (many perf-iota : (subterm many (Nat) k) (erased (List (U8)) bs) (unique (Bytes bs) b)
    (erased (Length (U8) bs u8-modulus) len) (erased (Lt k (Succ u8-modulus)) le) ->
    (erased (List (U8)) bs2) (unique (Bytes bs2) b2 at b) (erased (Length (U8) bs2 u8-modulus) len2))
  (let-match many k (Succ k1) ((Zero) (values bs b len)))
  (let-match erased le (LtS _ _ lt1))
  (let ((erased _) (erased slot)) (nth-exists _ _ _ _ len lt1))
  (let ((erased bs1) (unique b1) (erased set)) (bytes-set _ b k1 (MkU8 k1 lt1) _ slot))
  (tail $ perf-iota k1 bs1 b1 (setnth-length _ _ _ _ _ _ set len) (lt-weaken _ _ lt1)))

(let ((erased _) (unique perf-bytes-u0) (erased perf-bytes-rep)) (bytes-make u8-modulus (MkU8 0 perf-zero-u8)))
(let ((erased _) (unique perf-bytes-u) (erased perf-bytes-len))
  (perf-iota u8-modulus _ perf-bytes-u0 (repeat-length _ _ _ _ perf-bytes-rep) (lt-succ u8-modulus)))
(let ((many perf-bytes)) (MkPerfAlphabet _ (share perf-bytes-u) u8-modulus perf-bytes-len u8-modulus-pos))

(def-fns _ $ (many perf-next : (many (Nat) s) -> (many (Nat) r))
  (let ((many r) (erased _) (erased _)) (nat-mod (nat-add (nat-mul s 1103515245) 12345) 1073741824 perf-range-pos))
  r)

(def-fns _ $ (many perf-pick : (many (PerfAlphabet) al) (many (Nat) v) -> (many (U8) x))
  (let-match many al (MkPerfAlphabet _ a n len pos))
  (let ((many h) (erased _) (erased _) (erased _) (erased _) (erased _)) (div v 1048576 perf-high-pos))
  (let ((many j) (erased below) (erased _)) (nat-mod h n pos))
  (let ((erased _) (erased nth)) (nth-exists _ _ _ _ len below))
  (bytes-get-many _ a j _ nth))

(def-fns _ $ (many perf-step : (many (Nat) r) (many (Nat) q) -> (many (Nat) r1) (many (Nat) v))
  (let ((many h) (erased _) (erased _) (erased _) (erased _) (erased _)) (div q 1024 perf-low-pos))
  (let ((many e) (erased _) (erased _)) (nat-mod h 331 perf-period-pos))
  (let ((many r1)) (perf-next r))
  (let-match many e (Succ e1) ((Zero) (let ((many r2)) (perf-next r1)) (values r2 r2)))
  (let-match many e1 (Succ e2) ((Zero) (values r1 q)))
  (let-match many e2 (Succ _) ((Zero) (values r q)))
  (values r1 r1))

(def-fns _ $ (many perf-fill : (many (PerfAlphabet) al) (subterm many (Nat) k) (many (Nat) r) (many (Nat) q) (erased (Nat) n)
    (erased (List (U8)) bs) (unique (Bytes bs) b) (erased (Length (U8) bs n) len) (erased (Lt k (Succ n)) le) ->
    (erased (List (U8)) bs2) (unique (Bytes bs2) b2 at b) (erased (Length (U8) bs2 n) len2))
  (let-match many k (Succ k1) ((Zero) (values bs b len)))
  (let-match erased le (LtS _ _ lt1))
  (let ((many q1)) (perf-next q))
  (let ((many r1) (many v)) (perf-step r q1))
  (let ((erased _) (erased slot)) (nth-exists _ _ _ _ len lt1))
  (let ((erased bs1) (unique b1) (erased set)) (bytes-set _ b k1 (perf-pick al v) _ slot))
  (tail $ perf-fill al k1 r1 q1 n bs1 b1 (setnth-length _ _ _ _ _ _ set len) (lt-weaken _ _ lt1)))

(def-fns _ $ (many perf-text : (many (PerfAlphabet) al) (many (Nat) n) (erased (Lt n max-array-length) fits)
    (many (Nat) r) (many (Nat) q) -> (erased (List (U8)) bs) (many (Text bs) s))
  (let ((erased bs0) (unique b0) (erased rep)) (bytes-make n (MkU8 0 perf-zero-u8)))
  (let ((erased bs) (unique b) (erased len)) (perf-fill al n r q n bs0 b0 (repeat-length _ _ _ _ rep) (lt-succ n)))
  (values bs (MkText bs (share b) n len fits)))

(def-fns _ $ (many perf-line : (many (String) label) (many (Nat) v) (many (String) rest) -> (many (String) s))
  (str-append label (str-append " " (str-append (nat-str v) (str-append "\n" rest)))))

(def-fns _ $ (many perf-minus : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let-match many (lt-dec b (Succ a)) (Yes _ _ le) ((No _ _ _) 0))
  (let ((many c) (erased _)) (sub a b le))
  c)

(def-lvl Perf)

(def-unique Perf $ (unique perf-start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program Perf) next))
  (let ((erased a1) (many s1)) (perf-text perf-letters 3000 (prove-literal-lt 3000 18014398509481984) 42 1))
  (let ((erased b1) (many t1)) (perf-text perf-letters 2800 (prove-literal-lt 2800 18014398509481984) 7 2))
  (let ((erased a2) (many s2)) (perf-text perf-letters 20000 (prove-literal-lt 20000 18014398509481984) 11 3))
  (let ((erased b2) (many t2)) (perf-text perf-letters 400 (prove-literal-lt 400 18014398509481984) 13 4))
  (let ((erased a3) (many s3)) (perf-text perf-letters 400 (prove-literal-lt 400 18014398509481984) 17 5))
  (let ((erased b3) (many t3)) (perf-text perf-letters 20000 (prove-literal-lt 20000 18014398509481984) 19 6))
  (let ((erased a4) (many s4)) (perf-text perf-letters 3000 (prove-literal-lt 3000 18014398509481984) 23 7))
  (let ((erased b4) (many t4)) (perf-text perf-letters 3000 (prove-literal-lt 3000 18014398509481984) 23 8))
  (let ((erased a5) (many s5)) (perf-text perf-cases 3000 (prove-literal-lt 3000 18014398509481984) 29 9))
  (let ((erased b5) (many t5)) (perf-text perf-cases 2800 (prove-literal-lt 2800 18014398509481984) 31 10))
  (let ((erased a6) (many s6)) (perf-text perf-bytes 3000 (prove-literal-lt 3000 18014398509481984) 37 11))
  (let ((erased b6) (many t6)) (perf-text perf-bytes 2800 (prove-literal-lt 2800 18014398509481984) 41 12))
  (let ((unique stop)) (Measure (Stop)))
  (let ((unique w1) (many u0)) (world-do _ w (Measure (Start))))
  (let ((many d1) (erased _)) (edit-distance-fast a1 s1 b1 t1))
  (let ((many d2) (erased _)) (edit-distance-fast a2 s2 b2 t2))
  (let ((many d3) (erased _)) (edit-distance-fast a3 s3 b3 t3))
  (let ((many d4) (erased _)) (edit-distance-fast a4 s4 b4 t4))
  (let ((many d5) (erased _)) (edit-distance-fast a5 s5 b5 t5))
  (let ((many d6) (erased _)) (edit-distance-fast a6 s6 b6 t6))
  (let ((unique w2) (many u1)) (world-do _ w1 stop))
  (let-match many u0 (MkUsage wall0 user0 sys0 minor0 promoted0 major0 minor-gcs0 major-gcs0))
  (let-match many u1 (MkUsage wall1 user1 sys1 minor1 promoted1 major1 minor-gcs1 major-gcs1))
  (let ((many text))
    (perf-line "random-distance" d1 $ perf-line "long-short-distance" d2 $ perf-line "short-long-distance" d3
      $ perf-line "near-equal-distance" d4 $ perf-line "case-only-distance" d5 $ perf-line "all-bytes-distance" d6
      $ perf-line "wall-ns" (perf-minus wall1 wall0) $ perf-line "user-ns" (perf-minus user1 user0) $ perf-line "sys-ns" (perf-minus sys1 sys0)
      $ perf-line "minor-words" (perf-minus minor1 minor0) $ perf-line "promoted-words" (perf-minus promoted1 promoted0)
      $ perf-line "major-words" (perf-minus major1 major0)
      $ perf-line "minor-gcs" (perf-minus minor-gcs1 minor-gcs0) $ perf-line "major-gcs" (perf-minus major-gcs1 major-gcs0) ""))
  (let ((unique w3) (many _)) (world-do _ w2 (WriteOut text)))
  (values w3 (Exit Perf (MkU8 0 perf-zero-u8))))

(Continue Perf perf-start)
