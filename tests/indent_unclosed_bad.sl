; error: missing `)`
; warns: tests/indent_unclosed_bad.sl:11:1: warning: same indentation (0) as the previous checked line but nesting is 1, expected 0 (matching that line)
; warns: tests/indent_unclosed_bad.sl:10:1: note: the previous line at this indentation
; warns: tests/indent_unclosed_bad.sl:10:1: warning: this form is never closed
; A file the reader refuses still has its indentation checked: the syntax error names one form that was left
; open, while the warnings name the line whose nesting does not match its indentation, the line it is checked
; against, and every form the file leaves open, so that each missing ) has a place to go.

(def-lvl A)
(let ((many x)) (Zero)
(Zero)
