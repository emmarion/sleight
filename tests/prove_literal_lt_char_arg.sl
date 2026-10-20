; expect: 0
; A character stands for its code.

(let ((erased (Lt 97 98) q)) (prove-literal-lt #\a 98))
(Zero)
