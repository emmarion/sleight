; `dump-context` as the only statement: the program has bound nothing, so the prelude's entries are listed.
(dump-context)
; error: tests/dump_context_empty.sl:2:1: error: `dump-context` stops elaboration here and reports what the checker knows
; error: goal: none; `dump-context` stands as a statement here, so nothing is expected of it
; error: in scope, newest first (the program has bound nothing, so the prelude's <**> are listed):
; error: Univ : (TyCtor -> Type)  [erased, Const, type constructor, built in]
; error: Type : (Univ)  [erased, Const, type, built in]
; error: is (Univ)
; error: Cons : (ValCtor (erased (Univ) A) (many A head) (many (List A) rest) -> (List A))  [many, Const, constructor, bound at lib/prelude.sl:<**>]
; error: at-database: every entry is at a location of its own
; error: opened (the program has bound nothing, so the prelude's <**> are listed): <**>(Matchable enum List (many Nil) (many Cons))
