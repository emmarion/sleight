; prelude: none
; error: needs the prelude's `Request`
(def-lvl P)
(def-fns P $ (many f : (unique (World) w at vacant-slot) -> (unique (World) w2 at w)) (world-do _ w w))
