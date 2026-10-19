;! file "a.sl"
(let ((many x)) (Zero))
;! file "b.sl" and more
x
; error: a.sl:2:1: syntax error: `;! file` takes one string literal, the file's name
