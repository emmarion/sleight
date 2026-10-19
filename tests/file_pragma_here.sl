; needs: ../std/macro macro_lib
(warn-here)
;! file "claimed/here.sl"

(warn-here)
; warns: tests/file_pragma_here.sl:2:1: warning: here
; warns: claimed/here.sl:2:1: warning: here
