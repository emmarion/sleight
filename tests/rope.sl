; stdin: x
; expect: hello, world
; A Rope, with a character leaf, flattened by the FFI in one pass (section 41), with the Flat proof relating the tree to the string
; through Append; the model runs under --no-extern.

(def-lvl L)
(def-fns L $ many main : (many (String) input) -> (many (String) out)
  (let (many r) (RCat (RStr "hello") (RCat (REmpty) (RCat (RStr ", ") (RCat (RStr "world") (RChar #\newline))))))
  (let (many s) (erased (Flat r s) p) (flatten r))
  s)
main
