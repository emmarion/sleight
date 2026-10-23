; needs: ../std/macro
; error: std/macro.sl:<**>: error: `BTrue` is not a constructor of `Nat`
; error: tests/macro_frame_chain_bad.sl:9:7: note: in the expansion of `and` here
; error: tests/macro_frame_chain_bad.sl:12:7: note: in the expansion of `both` here
; error: tests/macro_frame_chain_bad.sl:14:3: note: in the expansion of `twice` here
(def-macro (both args)
  (let-match many args (Cons _ a r1) ((Nil _) (qq (BTrue))))
  (let-match many r1 (Cons _ b _) ((Nil _) (qq (BTrue))))
  (qq (and (~ a) (~ b))))
(def-macro (twice args)
  (let-match many args (Cons _ a _) ((Nil _) (qq (BTrue))))
  (qq (both (~ a) (~ a))))
(def-fns _ $ (many h : (many (Nat) x) -> (many (Bool) m))
  (twice x))
