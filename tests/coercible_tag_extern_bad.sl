; externs: only
; error: `SNil` is a constructor of an extern type, whose representation is the FFI's
(let ((erased _)) (coercible-tag (Shared) SNil))
(Zero)
