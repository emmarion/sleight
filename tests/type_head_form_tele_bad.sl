; error: tests/type_head_form_tele_bad.sl:4:12: error: no function is called while a type is elaborated, so a head in a type cannot be a form (section 9)
(def-fns _ $ (many pick : (many (Special) s) -> (many (Special) r)) s)
(def-fns _ $ (many f : (many (Special) s)
    (many ((pick s) (level-of pick) (many (Nat) a) -> (many (Nat) b)) g) -> (many (Nat) r)) 0)
