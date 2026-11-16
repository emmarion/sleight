(let ((many program)) (build "double" 5))
(let ((many fuelled)) (eval 1000 (ENil) program))
(comptime-match many fuelled (MkEvaled _ _ vs derivation))
(eval-by vs (ENil) program derivation)
