; error: expected a cell binder, got `(x)`
(let ((many b)) (BTrue))
(comptime-match many b (BTrue (x)))
b
