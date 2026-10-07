(def-fns _ $ (many accept-array : (erased (List (Nat)) xs) (erased (AllBelow xs u62-modulus) small)
    (erased (Nat) len) (erased (Length (Nat) xs len) lp) (erased (Lt len u62-modulus) fits)
    (erased (List (Copy (Nat))) cs) (unique (Array (Copy (Nat)) cs) a) (erased (Copies xs cs) rel) ->
    (many (Nat) n) (erased (LongestPalindrome xs n) correct))
  (let ((many n) (erased correct)) (longest-palindrome-fast xs small len lp fits cs a rel))
  (values n correct))
