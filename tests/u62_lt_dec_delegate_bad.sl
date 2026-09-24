; error: `u62-lt-dec` has no `Delegate` proof in scope
; An extern's model is only its specification: the FFI runs a native-int operation that is correct only under
; the erased bounds, so a Delegate proof to the unbounded Nat primitive would let a coerce drop those bounds.
(let ((erased cg)) (coercible-of (delegate-of u62-lt-dec)))
(Zero)
