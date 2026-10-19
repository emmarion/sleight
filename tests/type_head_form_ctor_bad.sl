; error: tests/type_head_form_ctor_bad.sl:5:39: error: no function is called while a type is elaborated, so a head in a type cannot be a form (section 9)
(def-fns _ $ (many pick : (many (Special) s) -> (many (Special) r)) s)
(def-fns _ $ (many inc : (many (Nat) a) -> (many (Nat) b)) (Succ a))
(def-adts $ (Box : -> Type) enum
  (many B : (many (Special) s) (many ((pick s) (level-of inc) (many (Nat) a) -> (many (Nat) b)) g) -> (Box)))
