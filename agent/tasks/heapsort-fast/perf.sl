; Length of the array to sort.
(let ((many perf-size)) 1048576)

(let ((erased (Lt perf-size u62-modulus) perf-size-fits)) (prove-literal-lt 1048576 4611686018427387904))
(let ((erased perf-range-fits)) (prove-literal-lt 1073741824 4611686018427387904))
(unary 0)
(let ((erased perf-range-pos)) (prove-literal-lt 0 1073741824))
(let ((erased (Lt 0 u8-modulus) perf-zero-u8)) u8-modulus-pos)

;! suppress warn Nat
;! suppress warn nat-add
;! suppress warn nat-mul
;! suppress warn nat-mod

(def-fns _ $ (many perf-gen : (subterm many (Nat) k) (many (Nat) seed) (erased (Nat) j) (erased (Add k j perf-size) count)
    (erased (List (Nat)) xs) (erased (AllTo (Nat) Lt xs u62-modulus) small) (erased (Length (Nat) xs j) len)
    (many (List (Copy (Nat))) cs) (erased (Copies (Nat) xs cs) rel) ->
    (erased (List (Nat)) xs2) (erased (AllTo (Nat) Lt xs2 u62-modulus) small2) (erased (Length (Nat) xs2 perf-size) len2)
    (many (List (Copy (Nat))) cs2) (erased (Copies (Nat) xs2 cs2) rel2))
  (let-match many k (Succ k1) ((Zero) (let-match erased count (AddZero _)) (values xs small len cs rel)))
  (let-match erased count (AddSucc _ _ total1 count1))
  (let ((many x) (erased x-below) (erased _)) (nat-mod (nat-add (nat-mul seed 1103515245) 12345) 1073741824 perf-range-pos))
  (tail $ perf-gen k1 x _ (add-succ-right _ _ _ count1)
    _ (AllToCons _ _ x xs _ (lt-trans _ _ _ x-below perf-range-fits) small) (LengthCons _ _ _ _ len)
    (Cons _ (MkCopy _ x) cs) (CopiesCons _ _ _ _ rel)))

(def-fns _ $ (erased perf-nth-exists : (erased Type A) (erased (List A) xs) (erased (Nat) n) (subterm erased (Length A xs n) l)
    (erased (Nat) i) (erased (Lt i n) lt) -> (erased A x) (erased (Nth A xs i x) p))
  (let-match erased l (LengthCons _ y rest n1 l1) (absurd (LengthNil _) lt))
  (let-match erased i (Succ i1) ((Zero) (values y (NthHere _ _ _))))
  (let-match erased lt (LtS _ _ lt1))
  (let ((erased x) (erased p)) (perf-nth-exists _ _ _ l1 i1 lt1))
  (values x (NthThere _ _ _ _ _ p)))

(def-fns _ $ (many perf-checksum : (erased (List (Copy (Nat))) ds) (many (Array (Copy (Nat)) ds) r)
    (erased (Nat) n) (erased (Length (Copy (Nat)) ds n) len) (subterm many (Nat) k) (erased (Lt k (Succ n)) le)
    (many (Nat) acc) -> (many (Nat) sum))
  (let-match many k (Succ k1) ((Zero) acc))
  (let-match erased le (LtS _ _ lt1))
  (let ((erased x) (erased nth)) (perf-nth-exists _ _ _ len k1 lt1))
  (let-match many (array-get-many _ _ r k1 _ nth) (MkCopy _ v))
  (tail $ perf-checksum _ r _ len k1 (lt-weaken _ _ lt1) (nat-add acc (nat-mul k v))))

(def-fns _ $ (many perf-line : (many (String) name) (many (Nat) v) (many (String) rest) -> (many (String) s))
  (str-append name (str-append " " (str-append (nat-str v) (str-append "\n" rest)))))

;! suppress warn Succ
;! suppress warn lt-dec
;! suppress warn sub
(def-fns _ $ (many perf-minus : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let-match many (lt-dec b (Succ a)) (Yes _ _ le) ((No _ _ _) 0))
  (let ((many c) (erased p)) (sub a b le))
  c)
;! restore warn sub
;! restore warn lt-dec
;! restore warn Succ

(def-lvl Perf)

(def-unique Perf $ (unique perf-start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program Perf) next))
  (let ((erased xs) (erased small) (erased len) (many cs) (erased rel))
    (perf-gen perf-size 42 _ (add-zero-right _) _ (AllToNil _ _ _) (LengthNil _) (Nil _) (CopiesNil _)))
  (let ((unique a)) (list-to-array _ cs))
  (let ((unique w1) (many u0)) (world-do _ w (Measure (Start))))
  (let ((erased ys) (erased ds) (unique r) (erased rel2) (erased correct)) (accept xs small _ len perf-size-fits cs a rel))
  (let ((unique w2) (many u1)) (world-do _ w1 (Measure (Stop))))
  (let ((many rs)) (share r))
  (let ((many n) (erased len2)) (array-length-many _ _ rs))
  (let-match many u0 (MkUsage wall0 user0 sys0 minor0 promoted0 major0 minor-gcs0 major-gcs0))
  (let-match many u1 (MkUsage wall1 user1 sys1 minor1 promoted1 major1 minor-gcs1 major-gcs1))
  (let ((many text))
    (perf-line "checksum" (perf-checksum _ rs _ len2 n (lt-succ n) 0)
      $ perf-line "wall-ns" (perf-minus wall1 wall0) $ perf-line "user-ns" (perf-minus user1 user0) $ perf-line "sys-ns" (perf-minus sys1 sys0)
      $ perf-line "minor-words" (perf-minus minor1 minor0) $ perf-line "promoted-words" (perf-minus promoted1 promoted0)
      $ perf-line "major-words" (perf-minus major1 major0)
      $ perf-line "minor-gcs" (perf-minus minor-gcs1 minor-gcs0) $ perf-line "major-gcs" (perf-minus major-gcs1 major-gcs0) ""))
  (let ((unique w3) (many _)) (world-do _ w2 (WriteOut text)))
  (values w3 (Exit Perf (MkU8 0 perf-zero-u8))))

(Continue Perf perf-start)
