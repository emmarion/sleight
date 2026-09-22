; needs: ../self/base ../pal/palindrome_relations ../pal/palindrome_naive ../pal/palindrome_lemmas ../pal/palindrome_centers ../pal/palindrome_seed ../pal/palindrome_manacher
; expect: (Cons _ 0 $ Cons _ 1 $ Cons _ 2 $ Cons _ 1 $ Cons _ 3 $ Cons _ 4 $ Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 2 $ Cons _ 5 $ Cons _ 5 $ Cons _ 5 $ Cons _ 6 $ Cons _ 1 $ Cons _ 3 $ Cons _ 5 $ Cons _ 13 $ Cons _ 10 $ Cons _ 7 $ Cons _ 11 $ Cons _ 9 $ Cons _ 6 $ Cons _ 12 $ Cons _ 8 $ Cons _ 6 $ Cons _ 9 $ Nil _)
; The nullary main makes these runtime checks in extracted programs too.
; Covers empty/singleton, odd/even, unequal outer/inner ends, ties, repeated
; elements, longest windows at the beginning, middle, and end, and nested
; mirrors that stop before, at, and beyond the rightmost boundary.

(def-fns _ $ many man-test-nats : (subterm many (String) s) ->
    (many (List (Nat)) xs)
  (match many s _
    ((SNil) (Nil (Nat)))
    ((SCons ch rest)
      (let-match many ch (MkChar byte))
      (let-match many byte (MkU8 n bound))
      (Cons (Nat) n (man-test-nats rest)))))

(def-fns _ $ many man-test-length : (many (String) s) -> (many (Nat) n)
  (let (many xs) (man-test-nats s))
  (let (many (Nat) n) (erased (LongestPalindrome xs n) correct)
    (longest-palindrome-manacher xs))
  n)

(def-fns _ $ many man-test-main : -> (many (List (Nat)) answers)
  $ Cons _ (man-test-length "") $
  Cons _ (man-test-length "a") $
  Cons _ (man-test-length "aa") $
  Cons _ (man-test-length "ab") $
  Cons _ (man-test-length "aba") $
  Cons _ (man-test-length "abba") $
  Cons _ (man-test-length "abca") $
  Cons _ (man-test-length "aabca") $
  Cons _ (man-test-length "babad") $
  Cons _ (man-test-length "cbbd") $
  Cons _ (man-test-length "abcbaq") $
  Cons _ (man-test-length "qabcbaz") $
  Cons _ (man-test-length "qabcba") $
  Cons _ (man-test-length "aaaaaa") $
  Cons _ (man-test-length "abcdef") $
  Cons _ (man-test-length "abacdfgdcaba") $
  Cons _ (man-test-length "abcxyzyxdef") $
  Cons _ (man-test-length "abacababacaba") $
  Cons _ (man-test-length "forgeeksskeegfor") $
  Cons _ (man-test-length "abacabaq") $
  Cons _ (man-test-length "abababababab") $
  Cons _ (man-test-length "aaaaabaaaa") $
  Cons _ (man-test-length "aabbaaqqabba") $
  Cons _ (man-test-length "abacabbacaba") $
  Cons _ (man-test-length "abcddcbaefggfe") $
  Cons _ (man-test-length "abaxyzzyxf") $
  Cons _ (man-test-length "babcbabcbaccba") $
  Nil (Nat))

man-test-main
