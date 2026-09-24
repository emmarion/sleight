(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) n) -> (Box)))

(let ((many b))
  ;! warn MkBox slow
  (MkBox 3))

b
; error: `;! warn` must be written between top-level forms
