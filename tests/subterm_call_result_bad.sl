; error: is not a strict subterm of
; A field is a subterm of the value it was destructured from; the result of a call is not. The result is
; a fresh entry with no rule relating it to the scrutinee (DESIGN.md section 15), so a structure whose
; recursive occurrence is reached by calling a stored function cannot drive recursion the way
; recursion_through_pointer.sl's stored function does when the decreasing argument is a field.

(def-lvl AL)
(def-adts $ (Wrap : -> Type)
  enum
  (many MkWrap : (many (Fn AL -> (many (Wrap) w)) f) -> (Wrap)))

(def-lvl WL)
(let ((erased aw)) (prove-predates AL WL))

(def-fns WL $ (many walk : (subterm many (Wrap) w) -> (many (Nat) n))
  (match many w _
    ((MkWrap f)
      (let ((many sub)) (f (predates aw)))
      (Succ (walk (subterm (prove-subterm sub w)) sub)))))
walk
