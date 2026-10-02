; error: `distinct`: 3 is the same literal twice, so there is nothing to refute
; error: hint: `distinct` refutes a context whose facts equate two different literals, typically an `absurd` branch or function body
; distinct refuses one literal given twice, whatever the context.

(let ((erased q)) (distinct 3 3))
(Zero)
