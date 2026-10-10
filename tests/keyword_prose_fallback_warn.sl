(let ((many notail)) (Zero))
(def-fns _ $ (many count : (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil _) (Zero))
    ((Cons _ h t) (Succ (count t)))))
(Zero)
; expect: 0
; warns: tests/keyword_prose_fallback_warn.sl:1:7: warning: declaration of `notail` shadows a built-in
; warns: tests/keyword_prose_fallback_warn.sl:5:25: warning: same-level call to `count` is unmarked; mark it `__notail`
; warns: tests/keyword_prose_fallback_warn.sl:1:7: note: `__notail` is `notail`, shadowed here
