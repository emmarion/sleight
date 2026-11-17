let rec f (n:int) (a:int) = if n = 0 then a else 1 + f (n-1) a
let () = print_int (f 10_000_000 1)
