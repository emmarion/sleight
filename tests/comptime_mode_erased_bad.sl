; error: `comptime-match` needs a non-erased multiplicity
(let ((many z)) (Zero))
(comptime-match erased z (Zero))
