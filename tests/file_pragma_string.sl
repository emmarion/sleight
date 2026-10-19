(let ((many s)) "a
;! file \"claimed/no.sl\"
b")
s
; expect: "a\n;! file \"claimed/no.sl\"\nb"
