(let ((many src)) (Cons _ (Open) $ Cons _ (Open) $ Cons _ (Close) $ Cons _ (Close) $ Nil _))
(let ((many bad)) (Cons _ (Open) $ Cons _ (Close) $ Cons _ (Close) $ Nil _))
(MkPair _ _ (decide 0 src) (decide 0 bad))
