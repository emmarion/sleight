(def-fns _ $ (many f : (erased Type A) (many (List A) ys)
    (subterm many (List A) xs) (subterm many (List A) ws) -> (many (Nat) n))
  (match many xs _
    ((Nil a) (Zero))
    ((Cons a hd tl)
      (tail $ f A
        (subterm _) ys
        tl
        ws))))
; error: tests/msg_subterm_not_param_bad.sl:7:9: error: argument 2, `ys`, of `f` is not a `subterm` parameter
; error: tests/msg_subterm_not_param_bad.sl:8:9: note: argument 3, `xs`, of `f` is a `subterm` parameter
; error: tests/msg_subterm_not_param_bad.sl:9:9: note: argument 4, `ws`, of `f` is a `subterm` parameter
; error: tests/msg_subterm_not_param_bad.sl:1:14: note: function `f` is declared here
