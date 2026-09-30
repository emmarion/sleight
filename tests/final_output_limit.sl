; confine-output-bytes: 3
; stderr: runtime error: output limit exceeded: this request would bring the program's approximate output to 6 bytes, over its limit of 3
; exit: 1
; A printed final value counts towards the limit, its newline included.
12345
