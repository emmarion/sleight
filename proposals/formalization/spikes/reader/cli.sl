(def-fns _ $ (many main : (many (String) text) -> (many (String) out))
  (str-append (show-read text) "\n"))

main
