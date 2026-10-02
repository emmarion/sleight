; `dump-context` where a type is expected: the goal is a type, and the position erased.
(def-fns _ $ (many first : (erased Type A) (many (dump-context) x) -> (many A r))
  x)
; error: tests/dump_context_type.sl:2:50: error: `dump-context` stops elaboration here and reports what the checker knows
; error: goal: a type, in an erased position
; error: position: erased
; error: A : Type  [erased, Dyn, type, bound at tests/dump_context_type.sl:2:28]
; error: at-database: every entry is at a location of its own
