; A complete distance row as an ERASED relation on the contents of an array.
; There is one cell for every suffix of ys, including the empty suffix, so
; an n-byte target has n+1 cells. Every live cell is Copy U62 (an immediate).
(def-adts $ (EdRow : ((List (U8)) xs) ((List (U8)) ys) ((List (Copy (U62))) cells) -> Type)
  enum
  (many EdRowNil : (erased (List (U8)) xs) (erased (Nat) d) (erased (Lt d u62-modulus) pd)
    (erased (Dist xs (Nil (U8)) d) dist) (erased (Lt d ed-value-limit) small) ->
    (EdRow xs (Nil (U8)) (Cons (Copy (U62)) (MkCopy (U62) (MkU62 d pd)) (Nil (Copy (U62))))))
  (many EdRowCons : (erased (List (U8)) xs) (erased (U8) y) (erased (List (U8)) ys)
    (erased (Nat) d) (erased (Lt d u62-modulus) pd) (erased (Dist xs (Cons (U8) y ys) d) dist)
    (erased (Lt d ed-value-limit) small) (erased (List (Copy (U62))) cells) (erased (EdRow xs ys cells) more) ->
    (EdRow xs (Cons (U8) y ys) (Cons (Copy (U62)) (MkCopy (U62) (MkU62 d pd)) cells))))

(def-fns _ $ (erased ed-row-head : (erased (List (U8)) xs ys) (erased (List (Copy (U62))) cells)
    (erased (EdRow xs ys cells) row) ->
    (erased (Nat) d) (erased (Lt d u62-modulus) pd) (erased (Lt d ed-value-limit) small)
    (erased (Nth (Copy (U62)) cells 0 (MkCopy (U62) (MkU62 d pd))) nth) (erased (Dist xs ys d) dist))
  (match erased row _
    ((EdRowNil _ d pd dist small) (values d pd small (NthHere _ _ _) dist))
    ((EdRowCons _ _ _ d pd dist small _ _) (values d pd small (NthHere _ _ _) dist))))

(def-fns _ $ (erased ed-row-at : (erased (List (U8)) xs ys) (erased (List (Copy (U62))) cells)
    (erased (EdRow xs ys cells) row) (erased (Nat) j) (erased (List (U8)) rest)
    (subterm erased (EdSuffix (U8) ys j rest) suffix) ->
    (erased (Nat) d) (erased (Lt d u62-modulus) pd) (erased (Lt d ed-value-limit) small)
    (erased (Nth (Copy (U62)) cells j (MkCopy (U62) (MkU62 d pd))) nth) (erased (Dist xs rest d) dist))
  (let-match erased suffix (EdSuffixThere _ _ ys1 k _ more) ((EdSuffixHere _ _) (ed-row-head xs ys cells row)))
  (let-match erased row (EdRowCons _ _ _ h ph _ _ cells1 row1))
  (let ((erased d) (erased pd) (erased small) (erased nth) (erased dist)) (ed-row-at xs ys1 cells1 row1 k rest more))
  (values d pd small (NthThere _ (MkCopy _ (MkU62 h ph)) cells1 k (MkCopy _ (MkU62 d pd)) nth) dist))

(def-fns _ $ (erased ed-row-length : (erased (List (U8)) xs ys) (erased (List (Copy (U62))) cells)
    (subterm erased (EdRow xs ys cells) row) (erased (Nat) n) (erased (Length (U8) ys n) len) ->
    (erased (Length (Copy (U62)) cells (Succ n)) length))
  (let-match erased row (EdRowCons _ _ ys1 d pd _ _ cells1 row1)
    ((EdRowNil _ d pd _ _)
      (let-match erased len (LengthNil _))
      (LengthCons _ (MkCopy _ (MkU62 d pd)) (Nil _) 0 (LengthNil _))))
  (let-match erased len (LengthCons _ _ _ n1 len1))
  (LengthCons _ (MkCopy _ (MkU62 d pd)) cells1 (Succ n1) (ed-row-length xs ys1 cells1 row1 n1 len1)))

; Borrowing a row array returns only its immediate Nat value at runtime.
(def-fns _ $ (many ed-row-get : (erased (List (U8)) xs ys) (erased (List (Copy (U62))) cells)
    (erased (EdRow xs ys cells) row) (unique (Array (Copy (U62)) cells) a)
    (many (Nat) j) (erased (List (U8)) rest) (erased (EdSuffix (U8) ys j rest) suffix) ->
    (many (Nat) d) (erased (Dist xs rest d) dist) (erased (Lt d ed-value-limit) small)
    (unique a is out at a))
  (let ((erased d) (erased pd) (erased small) (erased nth) (erased dist)) (ed-row-at xs ys cells row j rest suffix))
  (let ((many v) (unique out)) (array-get (U62) cells a j (MkU62 d pd) nth))
  (let-match many v (MkU62 value _))
  (values value dist small out))

; Write the cell immediately before an already computed suffix of an array.
; The caller supplies its newly proved Dist, then builds EdRowCons (or
; EdRowNil for the first write at column n). This helper never reads a byte
; or a cell at runtime, and always uses the immediate-only write primitive.
(def-fns _ $ (many ed-array-before : (erased (List (Copy (U62))) cells) (unique (Array (Copy (U62)) cells) a)
    (many (Nat) j) (erased (List (Copy (U62))) rest)
    (erased (EdSuffix (Copy (U62)) cells (Succ j) rest) suffix)
    (many (Nat) d) (erased (Lt d u62-modulus) pd) ->
    (erased (List (Copy (U62))) updated) (unique (Array (Copy (U62)) updated) out at a)
    (erased (EdSuffix (Copy (U62)) updated j (Cons (Copy (U62)) (MkCopy (U62) (MkU62 d pd)) rest)) new-suffix))
  (let ((erased old) (erased prev)) (ed-suffix-prev (Copy (U62)) cells j rest suffix))
  (let ((erased updated) (unique out) (erased set))
    (array-place-imm (Copy (U62)) cells a j (MkCopy (U62) (MkU62 d pd)) old
      (ed-suffix-nth (Copy (U62)) cells j old rest prev) (ImmCopy (U62) (ImmU62))))
  (values updated out (ed-suffix-set-before (Copy (U62)) cells j rest suffix (MkCopy (U62) (MkU62 d pd)) updated set)))
