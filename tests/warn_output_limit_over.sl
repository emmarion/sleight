; confine-output-bytes: 5
; stderr: runtime error: output limit exceeded: this request would bring the program's approximate output to 6 bytes, over its limit of 5
; exit: 1
; The compiler's own warnings are not in the totals the crash reports.
(compile-warn "a warning longer than the limit")
12345
; warns: tests/warn_output_limit_over.sl:5:1: warning: a warning longer than the limit
