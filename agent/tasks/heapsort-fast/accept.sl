(def-fns _ $ (many accept : (erased (List (Nat)) xs) (erased (AllBelow xs u62-modulus) small)
    (erased (Nat) n) (unique (Array (Copy (Nat)) n) a) (erased (ArrayIsList (Nat) xs n a) rel)
    (erased (Lt n u62-modulus) fits) ->
    (erased (List (Nat)) ys) (unique (Array (Copy (Nat)) n) r at a)
    (erased (ArrayIsList (Nat) ys n r) rel2) (erased (SortedPerm xs ys) correct))
  (let ((erased ys) (unique r) (erased rel2) (erased correct)) (heapsort-fast xs small n a rel fits))
  (values ys r rel2 correct))
