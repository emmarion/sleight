(def-fns _
  ((many g : (many (Nat) d) (subterm many (List (Nat)) xs) -> (many (Nat) n))
    (match many xs _
      ((Nil a) (Zero))
      ((Cons a hd tl) (tail $ h d xs (subterm _) tl))))
  ((many h : (many (Nat) e) (subterm many (List (Nat)) ys) (subterm many (List (Nat)) zs) -> (many (Nat) n))
    (Zero)))
(Zero)
; error: tests/msg_subterm_no_counterpart_bad.sl:5:38: error: argument 3, `zs`, of `h` is its `subterm` parameter 2, but the enclosing function `g` has only 1
; error: tests/msg_subterm_no_counterpart_bad.sl:6:4: note: function `h` is declared here
; error: tests/msg_subterm_no_counterpart_bad.sl:2:4: note: function `g` is declared here
