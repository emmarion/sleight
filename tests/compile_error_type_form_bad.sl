; error: tests/compile_error_type_form_bad.sl:2:60: error: no function is called while a type is elaborated, so a head in a type cannot be a form (section 9)
(def-fns _ $ (many f : (many (Nat) n) (many (compile-error (str-append "no" "!")) m) -> (many (Nat) r)) n)
