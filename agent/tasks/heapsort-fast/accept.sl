(def-fns _ $ (many accept : (erased (List (Nat)) xs) (erased (AllBelow xs u62-modulus) small)
    (erased (Nat) n) (erased (Length (Nat) xs n) len) (erased (Lt n u62-modulus) fits)
    (erased (List (Copy (Nat))) cs) (unique (Array (Copy (Nat)) cs) a) (erased (Copies xs cs) rel) ->
    (erased (List (Nat)) ys) (erased (List (Copy (Nat))) ds) (unique (Array (Copy (Nat)) ds) r at a)
    (erased (Copies ys ds) rel2) (erased (SortedPerm xs ys) correct))
  (let ((erased ys) (erased ds) (unique r) (erased rel2) (erased correct)) (heapsort-fast xs small n len fits cs a rel))
  (values ys ds r rel2 correct))
