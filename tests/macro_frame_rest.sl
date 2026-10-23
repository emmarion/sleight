; needs: ../std/macro
(def-fns _ $ (many old : (many (Nat) n) -> (many (Nat) r)) n)
;! warn old do not call old
(def-macro (zero-or args)
  (let-match many args (Cons _ x r1) ((Nil _) (Nil _)))
  (let-match many r1 (Cons _ d _) ((Nil _) (Nil _)))
  (qq (let-match many (~ x) (Zero) ((Succ _) (old (~ d))))))
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))
  (zero-or n n)
  (old n))
(f 0)
; expect: 0
; warns: tests/macro_frame_rest.sl:10:4: warning: call of `old`: do not call old
; warns: tests/macro_frame_rest.sl:3:1: note: `;! warn` for `old` is here
; warns: tests/macro_frame_rest.sl:7:47: warning: call of `old`: do not call old
; warns: tests/macro_frame_rest.sl:9:3: note: in the expansion of `zero-or` here
; warns: tests/macro_frame_rest.sl:3:1: note: `;! warn` for `old` is here
