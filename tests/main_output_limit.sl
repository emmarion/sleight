; confine-output-bytes: 3
; stdin: echo
; stderr: runtime error: output limit exceeded: this request would bring the program's approximate output to 4 bytes, over its limit of 3
; exit: 1
; A main final's output counts towards the limit as a WriteOut's does.
(def-fns _ $ (many main : (many (String) s) -> (many (String) r at s)) s)
main
