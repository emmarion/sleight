; stdin: world
; expect: Hello, world!
(def-fns _ $ (many main : (many (String) in) -> (many (String) out))
  (str-append "Hello, " $ str-append in "!\n"))

main
