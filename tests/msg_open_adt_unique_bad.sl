(def-fns _ $ (many f : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) C)
    (erased (ValCtor -> (T)) D)
    (unique (Matchable enum T (many C) (many D)) m)
    (many (T) x) -> (many (Nat) n))
  (open-adt unique m)
  (match many x (((Nat) r))
    ((C) 0)
    ((D) 1)))
; error: tests/msg_open_adt_unique_bad.sl:7:3: error: `__1`, declared `unique`, used at many without `share`
; error: tests/msg_open_adt_unique_bad.sl:6:3: note: `__1` is anonymous, minted here
; error: tests/msg_open_adt_unique_bad.sl:6:3: note: `__1` is declared here
