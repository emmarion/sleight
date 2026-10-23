; needs: ../std/macro
(def-macro (m _args) (qq (List (Nat))))
(m)
; error: tests/macro_handle_tyctor_bad.sl:2:26: error: type constructor `List` applied in a non-erased position
