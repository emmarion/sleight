; warns: tests/erased_kind_let_warn_bad.sl:4:7: warning: `T` is declared `many`, but a value of type `Type` is always erased, so it can be supplied only in an erased position; declare it `erased`
; error: erased

(let ((many Type T)) Type)
