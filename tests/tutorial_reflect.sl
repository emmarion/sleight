; expect: 7
(let ((many d)) (lt-dec 10 3))
(comptime-match many d (No _ _ _ _ le-q))
(let ((erased q)) (le-lt-succ _ _ le-q))
(let ((many c) (erased p)) (sub 10 3 q))
c
