; error: needs an ordinary `match`
; Stored values do not select a constructor: the opaque literal supplies no fact
; refuting either Nat constructor, so this still needs an ordinary match.

(let ((many x)) 5)
(let-match many x (Succ p))
(Zero)
