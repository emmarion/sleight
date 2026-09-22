; error: unbound name one
; A statement inside a let's right-hand side binds its name only within that right-hand side; the entry
; itself stays in scope after the let, anonymously (section 16).

(let ((many two))
  (let ((many one)) (Succ (Zero)))
  (Succ one))
one
