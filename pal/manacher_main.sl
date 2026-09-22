; String-to-String driver: read all stdin as bytes and print the longest
; palindrome length. Newlines, if present, are part of the input.
(def-fns _ $ (many manacher-reverse : (subterm many (List (Nat)) xs)
    (many (List (Nat)) acc) -> (many (List (Nat)) out))
  (match many xs _
    ((Nil a) acc)
    ((Cons a x rest) (tail (manacher-reverse rest (Cons _ x acc))))))

(def-fns _ $ (many manacher-input-acc : (subterm many (String) s)
    (many (List (Nat)) acc) -> (many (List (Nat)) xs))
  (match many s _
    ((SNil) (tail (manacher-reverse acc (Nil _))))
    ((SCons c rest)
      (tail (manacher-input-acc rest (Cons _ (char-code c) acc))))))

(def-fns _ $ (many manacher-input : (many (String) s) -> (many (List (Nat)) xs))
  (tail (manacher-input-acc s (Nil _))))

(def-fns _ $ (many manacher-main : (many (String) s) -> (many (String) out))
  (let ((many xs)) (manacher-input s))
  (let ((many n) (erased (LongestPalindrome xs n) correct))
    (longest-palindrome-manacher xs))
  (nat-str n))

manacher-main
