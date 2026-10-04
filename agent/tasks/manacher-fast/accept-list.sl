(def-fns _ $ (many accept-list : (many (List (Nat)) xs) -> (many (Nat) n) (erased (LongestPalindrome xs n) correct))
  (let ((many n) (erased correct)) (longest-palindrome-fast xs))
  (values n correct))
