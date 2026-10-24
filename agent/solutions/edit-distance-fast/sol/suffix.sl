; Generic erased suffixes, with forward offsets. For Bytes use A=U8;
; for distance arrays use A=Copy U62. No list here is traversed at runtime.
(def-adts $ (EdSuffix : (Type A) ((List A) whole) ((Nat) offset) ((List A) suffix) -> Type)
  enum
  (many EdSuffixHere : (erased Type A) (erased (List A) xs) -> (EdSuffix A xs 0 xs))
  (many EdSuffixThere : (erased Type A) (erased A x) (erased (List A) xs) (erased (Nat) i) (erased (List A) rest)
    (erased (EdSuffix A xs i rest) suffix) -> (EdSuffix A (Cons A x xs) (Succ i) rest)))

(def-fns _ $ (erased ed-suffix-length : (erased Type A) (erased (List A) whole) (erased (Nat) i) (erased (List A) rest)
    (subterm erased (EdSuffix A whole i rest) suffix) (erased (Nat) n) (erased (Length A whole n) len) ->
    (erased (Nat) k) (erased (Length A rest k) lr) (erased (Add i k n) sum))
  (let-match erased suffix (EdSuffixThere _ _ xs j _ more) ((EdSuffixHere _ _) (values n len (AddZero n))))
  (let-match erased len (LengthCons _ _ _ m lm))
  (let ((erased k) (erased lr) (erased sum)) (ed-suffix-length A xs j rest more m lm))
  (values k lr (AddSucc j k m sum)))

(def-fns _ $ (erased ed-suffix-nth : (erased Type A) (erased (List A) whole) (erased (Nat) i)
    (erased A x) (erased (List A) xs) (subterm erased (EdSuffix A whole i (Cons A x xs)) suffix) ->
    (erased (Nth A whole i x) nth))
  (let-match erased suffix (EdSuffixThere _ y rest j _ more) ((EdSuffixHere _ _) (NthHere A x xs)))
  (NthThere A y rest j x (ed-suffix-nth A rest j x xs more)))

(def-fns _ $ (erased ed-suffix-next : (erased Type A) (erased (List A) whole) (erased (Nat) i)
    (erased A x) (erased (List A) xs) (subterm erased (EdSuffix A whole i (Cons A x xs)) suffix) ->
    (erased (EdSuffix A whole (Succ i) xs) next))
  (let-match erased suffix (EdSuffixThere _ y rest j _ more)
    ((EdSuffixHere _ _) (EdSuffixThere A x xs 0 xs (EdSuffixHere A xs))))
  (EdSuffixThere A y rest (Succ j) xs (ed-suffix-next A rest j x xs more)))

(def-fns _ $ (erased ed-suffix-end : (erased Type A) (erased (List A) xs) (erased (Nat) n)
    (subterm erased (Length A xs n) len) -> (erased (EdSuffix A xs n (Nil A)) suffix))
  (let-match erased len (LengthCons _ x rest m lm) ((LengthNil _) (EdSuffixHere A (Nil A))))
  (EdSuffixThere A x rest m (Nil A) (ed-suffix-end A rest m lm)))

; Move a suffix boundary left by one element, without reading a live container.
(def-fns _ $ (erased ed-suffix-prev : (erased Type A) (erased (List A) whole) (erased (Nat) i) (erased (List A) xs)
    (subterm erased (EdSuffix A whole (Succ i) xs) suffix) ->
    (erased A x) (erased (EdSuffix A whole i (Cons A x xs)) prev))
  (let-match erased suffix (EdSuffixThere _ y rest _ _ more))
  (let-match erased i (Succ k)
    ((Zero) (let-match erased more (EdSuffixHere _ _)) (values y (EdSuffixHere A (Cons A y rest)))))
  (let ((erased x) (erased prev)) (ed-suffix-prev A rest k xs more))
  (values x (EdSuffixThere A y rest k (Cons A x xs) prev)))

; A runtime offset bound can expose the logical list shape, erased. This
; is useful in the lookahead branches that decide whether a swap is possible.
(def-fns _ $ (erased ed-suffix-nonempty : (erased Type A) (erased (List A) whole) (erased (Nat) n)
    (erased (Length A whole n) len) (erased (Nat) i) (erased (List A) rest)
    (subterm erased (EdSuffix A whole i rest) suffix) (erased (Lt i n) inside) ->
    (erased A x) (erased (List A) xs) (erased (Eq (List A) rest (Cons A x xs)) shape))
  (let-match erased suffix (EdSuffixThere _ _ ys j _ more)
    ((EdSuffixHere _ _)
      (let-match erased len (LengthCons _ x xs _ _) (absurd (LengthNil _) inside))
      (values x xs (Refl _ rest))))
  (let-match erased len (LengthCons _ _ _ m lm))
  (let-match erased inside (LtS _ _ jm))
  (ed-suffix-nonempty A ys m lm j rest more jm))

; Replacing the element just BEFORE a known suffix leaves that suffix alone.
; This is the core invariant update for a right-to-left array-writing loop.
(def-fns _ $ (erased ed-suffix-set-before : (erased Type A) (erased (List A) whole) (erased (Nat) i)
    (erased (List A) rest) (erased (EdSuffix A whole (Succ i) rest) suffix)
    (erased A v) (erased (List A) updated) (subterm erased (SetNth A whole i v updated) set) ->
    (erased (EdSuffix A updated i (Cons A v rest)) new-suffix))
  (let-match erased suffix (EdSuffixThere _ x xs _ _ more))
  (let-match erased set (SetThere _ _ _ k _ ys set1)
    ((SetHere _ _ _ _) (let-match erased more (EdSuffixHere _ _)) (EdSuffixHere A (Cons A v rest))))
  (EdSuffixThere A x ys k (Cons A v rest) (ed-suffix-set-before A xs k rest more v ys set1)))
