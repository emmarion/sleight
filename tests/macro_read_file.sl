; needs: ../std/macro macro_lib macro_read_file_lib
; expect: (Cons _ "; expect: \"data\"\n; tests/macro_read_file.sl reads this file as text.\n\"data\"\n" $ Cons _ "; expect: \"data\"\n; tests/macro_read_file.sl reads this file as text.\n\"data\"\n" $ Cons _ "Fail: ../dune: outside the directory ../tests" $ Cons _ "Fail: /etc/hostname: outside the directory ../tests" $ Cons _ "Fail: missing.txt: No such file or directory" $ Cons _ "Fail: no position to read relative to" $ Cons _ "Fail: elsewhere.sl: not a source file or a name given to --comptime-unconfine" $ Nil _)
; A macro reads a file relative to the source file of the position it gives, inside that file's directory.
(let ((many near)) (include "macro_read_file_data.sl"))
(let ((many back-in)) (include "../tests/macro_read_file_data.sl"))
(let ((many up)) (include "../dune"))
(let ((many absolute)) (include "/etc/hostname"))
(let ((many missing)) (include "missing.txt"))
(let ((many nowhere)) (include-nowhere "macro_read_file_data.sl"))
(let ((many elsewhere)) (include-elsewhere "macro_read_file_data.sl"))
(Cons _ near $ Cons _ back-in $ Cons _ up $ Cons _ absolute $ Cons _ missing $ Cons _ nowhere $ Cons _ elsewhere $ Nil _)
