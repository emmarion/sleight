(def-adts $ (Idle : ((List (Tok)) src) -> Type)
  enum
  (many MkIdle : (erased (List (Tok)) src) -> (Idle src)))

(def-lvl idle-lvl)

(def-fns idle-lvl $ (many start : (many (List (Tok)) src) -> (many (Idle src) s))
  (MkIdle src))

(def-fns idle-lvl $ (many step : (erased (List (Tok)) src) (many (Idle src) s) -> (many (Stepped Idle src) r))
  (More Idle src s))
