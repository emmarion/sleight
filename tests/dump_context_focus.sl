; `dump-context` with arguments shows those alone: a variable as its entry, any other term by what it
; canonicalizes to. The goal here holds a `_` still to solve, numbered and placed as in any message.
(def-fns _ $ (many rebuild : (erased Type A) (many (List A) xs) -> (many (List A) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ hd tl)
      (let ((many ys)) (Cons _ (dump-context xs (Cons A hd tl) tl nat-add) tl))
      ys)))
; error: tests/dump_context_focus.sl:7:32: error: `dump-context` stops elaboration here and reports what the checker knows
; error: goal: (many _?1 head)
; error: level: `_<**>`; the enclosing function has no subterm parameter
; error: xs : (List A)  [many, Dyn, value, bound at tests/dump_context_focus.sl:3:46]
; error: is (Cons A hd tl)
; error: `(Cons A hd tl)` canonicalizes to `(Cons A hd tl)` : `(List A)`
; error: tl : (List A)  [many, Dyn, value, bound at tests/dump_context_focus.sl:6:17]
; error: nat-add : (Fn nat-lvl (many (Nat) a) (many (Nat) b) -> (many (Nat) c))  [many, Const, function, bound at lib/prelude.sl:<**>]
; error: tests/dump_context_focus.sl:7:30: note: `_?1` is the `_` written here
