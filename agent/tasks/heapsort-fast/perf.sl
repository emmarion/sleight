; Length of the array to sort.
(let ((many perf-size)) 1048576)

(let ((many perf-size-cmp)) (nat-cmp perf-size u62m))
(comptime-match many perf-size-cmp (CLt _ _ _ _ perf-size-fits))
(let ((many perf-range-cmp)) (nat-cmp 1073741824 u62m))
(comptime-match many perf-range-cmp (CLt _ _ _ _ perf-range-fits))
(let ((many perf-range-pos-cmp)) (nat-cmp (Zero) 1073741824))
(comptime-match many perf-range-pos-cmp (CLt _ _ _ _ perf-range-pos))
(let ((many perf-zero-cmp)) (lt-dec 0 u8-modulus))
(comptime-match many perf-zero-cmp (Yes _ _ perf-zero-u8))

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

(def-adts $ (PerfSorted : -> Type)
  enum newtype
  (many PerfMkSorted : (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (List (Copy (Nat))) ds)
     (many (Array (Copy (Nat)) ds) r) (erased (Copies (Nat) ys ds) rel) (erased (SortedPerm (Nat) Le xs ys) correct) -> (PerfSorted)))

(def-lvl Perf)

(def-unique Perf $ (unique perf-report : (many (PerfSorted) s) (many (Usage) u) -> (unique (IO Perf) next))
  (let-match many s (PerfMkSorted _ _ _ r _ _))
  (let ((many n) (erased len)) (array-length-many _ _ r))
  (let-match many u (MkUsage wall-ns user-ns sys-ns minor-words promoted-words major-words minor-gcs major-gcs))
  (let ((many text))
    (perf-line "checksum" (perf-checksum _ r _ len n (lt-succ n) 0)
      $ perf-line "wall-ns" wall-ns $ perf-line "user-ns" user-ns $ perf-line "sys-ns" sys-ns
      $ perf-line "minor-words" minor-words $ perf-line "promoted-words" promoted-words $ perf-line "major-words" major-words
      $ perf-line "minor-gcs" minor-gcs $ perf-line "major-gcs" major-gcs ""))
  (WriteOut Perf text
    (unique-thunk _ _ (Exit Perf (MkU8 0 perf-zero-u8)))))

(def-unique Perf $ (unique perf-start : -> (unique (IO Perf) next))
  (let ((erased xs) (erased small) (erased len) (many cs) (erased rel))
    (perf-gen perf-size 42 _ (add-zero-right _) _ (AllToNil _ _ _) (LengthNil _) (Nil _) (CopiesNil _)))
  (let ((unique a)) (list-to-array _ cs))
  (def-unique _ $ (unique run : -> (many (PerfSorted) s))
    (let ((erased ys) (erased ds) (unique r) (erased rel2) (erased correct)) (accept xs small _ len perf-size-fits cs a rel))
    (PerfMkSorted xs ys ds (share r) rel2 correct))
  (Measure Perf _ _ run perf-report))

(Step Perf perf-start)
