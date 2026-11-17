let a : Obj.t = Obj.repr ("ab", 0, 2)
let b : Obj.t = Obj.repr ("ab", 0, 2)
let () = print_endline (if a == b then "shared" else "distinct")
