; `dump-context` inside a function body: the goal with its `at`, the level and subterm arguments, the branch's
; forced rule on the scrutinee, a consumed and a live unique cell, and the at-database's classes.
(def-fns _ $ (many append-into : (erased Type A)
    (unique (Cell Cons (SlotVacant) (SlotVacant)) cell)
    (many A h) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) r at cell))
  (match many xs _
    ((Nil _) (cell _ h ys))
    ((Cons _ hd tl)
      (let ((unique next)) (cell-alloc Cons))
      (let ((unique cell2)) (cell-write cell (Cons (SlotHolds h) (SlotHolds next))))
      (let ((many r2)) (tail (append-into _ next hd tl ys)))
      (dump-context))))
; error: tests/dump_context.sl:13:7: error: `dump-context` stops elaboration here and reports what the checker knows
; error: goal: (many (List A) r at cell)
; error: constructors of `List`: Nil : (ValCtor (erased (Univ) A) -> (List A)); Cons : (ValCtor (erased (Univ) A) (many A head) (many (List A) rest) -> (List A))
; error: position: many
; error: inside a function body or a match branch: binders here are Dyn and calls need their proofs
; error: level: `_<**>`; its subterm arguments, in order: `xs`
; error: r2 : (List A)  [many, Dyn, value, bound at tests/dump_context.sl:12:13]
; error: cell2 : (Cell Cons (SlotHolds h) (SlotHolds next))  [unique, Dyn, cell, bound at tests/dump_context.sl:11:13]
; error: unique: live, neither consumed nor shared on this path
; error: next : (Cell Cons (SlotVacant) (SlotVacant))  [unique, Dyn, cell, bound at tests/dump_context.sl:10:13]
; error: unique: consumed at tests/dump_context.sl:12:45, so usable only erased from here on
; error: xs : (List A)  [many, Dyn, value, subterm parameter 1 of the enclosing function, bound at tests/dump_context.sl:5:16]
; error: is (Cons A hd tl)
; error: cell : (Cell Cons (SlotVacant) (SlotVacant))  [unique, Dyn, cell, bound at tests/dump_context.sl:4:5]
; error: unique: consumed at tests/dump_context.sl:11:41, so usable only erased from here on
; error: A : (Univ)  [erased, Dyn, type, bound at tests/dump_context.sl:3:34]
; error: at-database, the entries at one location: {cell, _<**>, cell2} {xs, _<**>} {next, _<**>, r2}
