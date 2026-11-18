type t = K0 of { mutable f0 : Obj.t; mutable f1 : Obj.t } | K1 of { mutable f0 : Obj.t }
let rd (c : Obj.t) = match (Obj.obj c : t) with K0 { f0 = a; f1 = b } -> (a, b) | K1 { f0 = a } -> (a, a)
