; error: `distinct`: 3 and 4 do not canonicalize equally here, so there is nothing to refute
; error: hint: `distinct` refutes a context whose facts equate two different literals, typically an `absurd` branch or function body
; distinct only discharges a context that has already equated its two literals.

(let ((erased q)) (distinct 3 4))
(Zero)
