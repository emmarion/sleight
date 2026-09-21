; expect: (MkPair _ _ (Cons _ #\A $ Cons _ #\space $ Cons _ #\newline $ Cons _ #\tab $ Cons _ #\x01 $ Cons _ #\x28 $ Cons _ #\x29 $ Cons _ #\x3b $ Nil _) $ Cons _ "a\"b" $ Cons _ "back\\slash" $ Cons _ "tab\there" $ Cons _ "nl\nhere" $ Cons _ "" $ Nil _)
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
