; needs: ../pal/palindrome_relations ../pal/palindrome_naive
; expect: (Cons 0 (Cons 1 (Cons 2 (Cons 1 (Cons 3 (Cons 4 (Cons 1 (Cons 2 (Cons 3 (Cons 2 (Cons 5 (Cons 5 (Cons 5 (Cons 6 (Cons 1 (Cons 3 (Cons 5 (Nil))))))))))))))))))
; The nullary main makes these runtime checks in extracted programs too.
; Covers empty/singleton, odd/even, unequal outer/inner ends, ties, repeated
; elements, and longest windows at the beginning, middle, and end.

(def-fns _ $ many pal-test-nats : (subterm many (String) s) ->
    (many (List (Nat)) xs)
  (match many s _
    ((SNil) (Nil (Nat)))
    ((SCons ch rest)
      (let-match many ch (MkChar byte))
      (let-match many byte (MkU8 n bound))
      (Cons (Nat) n (pal-test-nats rest)))))

(def-fns _ $ many pal-test-length : (many (String) s) -> (many (Nat) n)
  (let (many xs) (pal-test-nats s))
  (let (many (Nat) n) (erased (LongestPalindrome xs n) correct)
    (longest-palindrome xs))
  n)

(def-fns _ $ many pal-test-main : -> (many (List (Nat)) answers)
  (Cons _ (pal-test-length "") $
  Cons _ (pal-test-length "a") $
  Cons _ (pal-test-length "aa") $
  Cons _ (pal-test-length "ab") $
  Cons _ (pal-test-length "aba") $
  Cons _ (pal-test-length "abba") $
  Cons _ (pal-test-length "abca") $
  Cons _ (pal-test-length "aabca") $
  Cons _ (pal-test-length "babad") $
  Cons _ (pal-test-length "cbbd") $
  Cons _ (pal-test-length "abcbaq") $
  Cons _ (pal-test-length "qabcbaz") $
  Cons _ (pal-test-length "qabcba") $
  Cons _ (pal-test-length "aaaaaa") $
  Cons _ (pal-test-length "abcdef") $
  Cons _ (pal-test-length "abacdfgdcaba") $
  Cons _ (pal-test-length "abcxyzyxdef") $
  Nil (Nat)))

pal-test-main
