; error: expected NoteOk, got (NoteBad #\x28 "a\"b\\c\nd\te")
; DESIGN.md section 15's diagnostics channel, where the payload of the variant that was not there is the
; message: a Char and a String in it spell as the literals they read back from (ASSUMPTIONS 154), the
; character being one of the delimiters a word cannot hold. tests/literal_print.sl pins the two spellings
; for a printed final; this is the same printer reached through the compile error, which slc reaches by its
; own compile-time path.

(def-adts $ (Note : -> Type)
  enum
  (many NoteOk : -> (Note))
  (many NoteBad : (many (Char) c) (many (String) s) -> (Note)))

(let ((many n)) (NoteBad #\x28 "a\"b\\c\nd\te"))

(comptime-match many n (NoteOk))
