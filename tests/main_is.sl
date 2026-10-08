; stdin: hello
; stdin: 
; expect: hello

(def-fns _ $ (many identity : (many (String) x) -> (many x is y)) x)
identity
