; error: `comptime-match` takes `many` or `unique`, not `erased`
(let ((many z)) (Zero))
(comptime-match erased z (Zero))
