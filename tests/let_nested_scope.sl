; error: unbound name one
; A statement inside a let's right-hand side binds only within that right-hand side (section 16).

(let (many two)
  (let (many one) (Succ (Zero)))
  (Succ one))
one
