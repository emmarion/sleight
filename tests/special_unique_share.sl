; expect: 1
(let ((unique u)) (%let))
((share u) ((many x)) (Zero))
((share u) ((many y)) (Succ x))
(let ((many z)) ((share u) ((many w)) (Succ y)) w)
(let ((unique v)) (%values))
(let ((many q)) ((share v) (Succ x)))
y
