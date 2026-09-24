(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

(let ((many b))
  ;! warn MkBox slow
  (MkBox 3))

b
; error: a pragma must be written between top-level forms
