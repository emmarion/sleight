; confine-output-bytes: 6
; expect: 12345
; The compiler's own warnings do not count towards the limit, under slc --interpret as in the reference.
(compile-warn "a warning longer than the limit")
12345
; warns: tests/warn_output_limit.sl:4:1: warning: a warning longer than the limit
