; prelude: none
; error: needs the prelude's `Request`
(def-lvl P)
(def-fns P $ (many f : (unique (World) w) -> (unique (World) w2 at w)) (world-do _ w w))
