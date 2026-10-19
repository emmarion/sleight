; error: tests/type_head_form_let_bad.sl:4:23: error: no function is called while a type is elaborated, so a head in a type cannot be a form (section 9)
(def-fns _ $ (many pick : (many (Special) s) -> (many (Special) r)) s)
(def-fns _ $ (many inc : (many (Nat) a) -> (many (Nat) b)) (Succ a))
(let ((many s) (many ((pick s) (level-of inc) (many (Nat) a) -> (many (Nat) b)) g)) (values Fn inc))
