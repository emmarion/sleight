(def-adts $ (Resumes : ((List (Tok)) src) ((Nat) depth) ((List (Tok)) rest) -> Type)
  enum
  (many ResStart : (erased (List (Tok)) src) -> (Resumes src (Zero) src))
  (many ResOpen : (erased (List (Tok)) src) (erased (Nat) d) (erased (List (Tok)) rest) (erased (Resumes src d (Cons (Tok) (Open) rest)) p) -> (Resumes src (Succ d) rest))
  (many ResClose : (erased (List (Tok)) src) (erased (Nat) d) (erased (List (Tok)) rest) (erased (Resumes src (Succ d) (Cons (Tok) (Close) rest)) p) -> (Resumes src d rest)))

(def-adts $ (Scan : ((List (Tok)) src) -> Type)
  enum
  (many MkScan : (erased (List (Tok)) src) (many (Nat) d) (many (List (Tok)) rest) (erased (Resumes src d rest) inv) -> (Scan src)))

(def-fns _ $ (erased resume-accepts : (erased (List (Tok)) src) (erased (Nat) d) (erased (List (Tok)) rest) (subterm erased (Resumes src d rest) inv) (erased (Accepts d rest) acc) -> (erased (Accepts (Zero) src) r))
  (match erased inv _
    ((ResStart _) acc)
    ((ResOpen _ d2 _ p) (resume-accepts src d2 (Cons (Tok) (Open) rest) p (AccOpen d2 rest acc)))
    ((ResClose _ _ _ p) (resume-accepts src (Succ d) (Cons (Tok) (Close) rest) p (AccClose d rest acc)))))

(def-fns _ $ (erased resume-fails : (erased (List (Tok)) src) (erased (Nat) d) (erased (List (Tok)) rest) (subterm erased (Resumes src d rest) inv) (erased (Fails d rest) bad) -> (erased (Fails (Zero) src) r))
  (match erased inv _
    ((ResStart _) bad)
    ((ResOpen _ d2 _ p) (resume-fails src d2 (Cons (Tok) (Open) rest) p (FailOpen d2 rest bad)))
    ((ResClose _ _ _ p) (resume-fails src (Succ d) (Cons (Tok) (Close) rest) p (FailClose d rest bad)))))

(def-lvl scan-lvl)

(def-fns scan-lvl $ (many start : (many (List (Tok)) src) -> (many (Scan src) s))
  (MkScan src (Zero) src (ResStart src)))

(def-fns scan-lvl $ (many step : (erased (List (Tok)) src) (many (Scan src) s) -> (many (Stepped Scan src) r))
  (let-match many s (MkScan _ d rest inv))
  (let-match many rest (Cons _ t more)
    ((Nil _)
      (match many d _
        ((Zero) (Done Scan src (Accepted _ _ (resume-accepts src d rest inv (AccEnd)))))
        ((Succ k) (Done Scan src (Rejected _ _ (resume-fails src d rest inv (FailUnclosed k))))))))
  (let-match many t (Close) ((Open) (More Scan src (MkScan src (Succ d) more (ResOpen src d more inv)))))
  (let-match many d (Succ k) ((Zero) (Done Scan src (Rejected _ _ (resume-fails src d rest inv (FailExtraClose more))))))
  (More Scan src (MkScan src k more (ResClose src k more inv))))
