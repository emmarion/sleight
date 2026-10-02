; error: needs a branch for it
; Stored values do not select a constructor: the opaque literal supplies no fact
; refuting either Nat constructor, so `Zero` still needs a branch.

(let ((many x)) 5)
(let-match many x (Succ p))
(Zero)
