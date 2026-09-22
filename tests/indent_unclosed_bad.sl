; error: missing )
; warns: tests/indent_unclosed_bad.sl:10:1: warning: same indentation (0) as the previous checked line but nesting is 1, expected 0 (matching that line)
; warns: tests/indent_unclosed_bad.sl: warning: final depth 1 (unclosed forms: append that many ))
; A file the reader refuses still has its indentation checked: the syntax error names only the form that was
; left open, while the warnings name the line whose nesting does not match its indentation and the count of
; forms never closed.

(def-lvl A)
(let ((many x)) (Zero)
(Zero)
