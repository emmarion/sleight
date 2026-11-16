(let ((many src)) (Cons _ (Open) $ Cons _ (Open) $ Cons _ (Open) $ Cons _ (Close) $ Cons _ (Close) $ Cons _ (Close) $ Nil _))
(let ((many s0)) (start src))
(def-unique program-lvl $ (unique go : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program program-lvl) p)) (drive src s0 w))
(Continue program-lvl go)
