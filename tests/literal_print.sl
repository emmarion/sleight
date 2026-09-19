; expect: ((Cons #\A (Cons #\space (Cons #\newline (Cons #\tab (Cons #\x01 (Cons #\x28 (Cons #\x29 (Cons #\x3b (Nil))))))))) (Cons "a\"b" (Cons "back\\slash" (Cons "tab\there" (Cons "nl\nhere" (Cons "" (Nil)))))))
; The spellings a printed Char and String read back from (ASSUMPTIONS 154): a bare character where the
; reader's word syntax admits one, the three named ones, and hexadecimal for a control character and for
; the delimiters a word cannot hold, which is why they are cut out of a string literal here rather than
; written; and the four escapes the reader unescapes.

(let (many s) "();")
(comptime-match many s (SCons op rest1))
(comptime-match many rest1 (SCons cl rest2))
(comptime-match many rest2 (SCons semi rest3))

(let (many chars)
  (Cons (Char) #\A $ Cons (Char) #\space $ Cons (Char) #\newline $ Cons (Char) #\tab
    $ Cons (Char) #\x01 $ Cons (Char) op $ Cons (Char) cl $ Cons (Char) semi $ Nil (Char)))

(let (many strs)
  (Cons (String) "a\"b" $ Cons (String) "back\\slash" $ Cons (String) "tab\there"
    $ Cons (String) "nl\nhere" $ Cons (String) "" $ Nil (String)))

(MkPair (List (Char)) (List (String)) chars strs)
