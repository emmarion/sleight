; needs: ../std/macro macro_lib
; error: unique value `em` has conflicting non-erased uses
(let ((unique em)) (MkMacro _ swap-fn))
(let ((many a)) ((share em) nat-add 1 2))
(let ((unique gone)) em)
a
