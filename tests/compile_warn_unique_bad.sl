; error: `u`, declared `unique`, used at many without `share`
; Reading a unique Const's message is a use at many, so it needs `share`.
;! suppress warn SCons
(let ((unique u)) (SCons #\u $ SNil))
(compile-warn u)
