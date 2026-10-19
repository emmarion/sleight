; needs: ../std/macro macro_lib macro_read_file_lib
;! file "claimed.sl"
(let ((many refused)) (include "dev/null"))
;! file "/unconfined.sl"
(let ((many unconfined)) (include "dev/null"))
;! file "/no-such-dir/unconfined.sl"
(let ((many missing)) (include "dev/null"))
(Cons _ refused $ Cons _ unconfined $ Cons _ missing $ Nil _)
; comptime-unconfine: /unconfined.sl
; comptime-unconfine: /no-such-dir/unconfined.sl
; expect: (Cons _ "Fail: claimed.sl: not a source file or a name given to --comptime-unconfine" $ Cons _ "" $ Cons _ "Fail: dev/null: no directory /no-such-dir" $ Nil _)
