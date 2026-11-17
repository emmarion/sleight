let[@inline never] f a b = a + b
let p x = print_int x; x
let () = ignore (f (p 1) (p 2)); print_newline ()
