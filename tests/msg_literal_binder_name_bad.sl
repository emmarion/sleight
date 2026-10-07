(let ((many five)) 5)
(coercible-wrap (Shared) five five)
; error: tests/msg_literal_binder_name_bad.sl:2:1: error: 5 is not a value constructor
