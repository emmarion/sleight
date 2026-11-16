(let ((many res)) (eval 1000 (ENil) program))
(comptime-match many res (MkEvaled _ _ vs p))
(eval-by (ENil) program vs p)
