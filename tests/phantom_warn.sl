; warns: warning (line 11): phantom constructor Tag has a non-erased field
; expect: (Boxed 3)
; A phantom constructor with a many field is legal and warned about (section 12): nothing non-erased is ever
; headed by Tag, so its field could not be read back. The program goes on to compile and run, which is the
; case the other warning test does not reach, its own program being refused.

(def-adts $ Box : -> Type
  enum
  (many Empty : -> (Box))
  (many Boxed : (many (Nat) n) -> (Box))
  (erased Tag : (many (Nat) n) -> (Box)))

(Boxed 3)
