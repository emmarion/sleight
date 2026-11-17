(def-lvl L)
(def-fns _ $ (many run-all : (subterm unique (Program L) p) (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (many (U8) code))
  (match unique p _
    ((Exit _ c) (values w c))
    ((Continue _ k)
      (let ((unique w1) (unique p2)) (k w))
      (run-all p2 w1))))
