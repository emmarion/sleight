; needs: ../std/macro
(def-macro (m args here mw extra)
  args)
; error: tests/macro_def_macro_usage_bad.sl:2:1: error: `def-macro` takes a header `(name args [here [mw]])` and a body
