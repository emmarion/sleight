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

(def-adts $ (StepsTo : ((List (Tok)) src) ((Scan src) s) ((Stepped Scan src) r) -> Type)
  enum
  (many StAccept : (erased (List (Tok)) src) (erased (Resumes src (Zero) (Nil (Tok))) inv) (erased (Accepts (Zero) src) acc)
     -> (StepsTo src (MkScan src (Zero) (Nil (Tok)) inv) (Done Scan src (Accepted (Zero) src acc))))
  (many StUnclosed : (erased (List (Tok)) src) (erased (Nat) k) (erased (Resumes src (Succ k) (Nil (Tok))) inv) (erased (Fails (Zero) src) bad)
     -> (StepsTo src (MkScan src (Succ k) (Nil (Tok)) inv) (Done Scan src (Rejected (Zero) src bad))))
  (many StOpen : (erased (List (Tok)) src) (erased (Nat) d) (erased (List (Tok)) more) (erased (Resumes src d (Cons (Tok) (Open) more)) inv)
     -> (StepsTo src (MkScan src d (Cons (Tok) (Open) more) inv) (More Scan src (MkScan src (Succ d) more (ResOpen src d more inv)))))
  (many StExtraClose : (erased (List (Tok)) src) (erased (List (Tok)) more) (erased (Resumes src (Zero) (Cons (Tok) (Close) more)) inv) (erased (Fails (Zero) src) bad)
     -> (StepsTo src (MkScan src (Zero) (Cons (Tok) (Close) more) inv) (Done Scan src (Rejected (Zero) src bad))))
  (many StClose : (erased (List (Tok)) src) (erased (Nat) k) (erased (List (Tok)) more) (erased (Resumes src (Succ k) (Cons (Tok) (Close) more)) inv)
     -> (StepsTo src (MkScan src (Succ k) (Cons (Tok) (Close) more) inv) (More Scan src (MkScan src k more (ResClose src k more inv))))))

(def-lvl scan-lvl)

(def-fns scan-lvl $ (many start : (many (List (Tok)) src) -> (many (Scan src) s))
  (MkScan src (Zero) src (ResStart src)))

(def-fns scan-lvl $ (many step : (erased (List (Tok)) src) (many (Scan src) s) -> (many (Stepped Scan src) r) (erased (StepsTo src s r) g))
  (let-match many s (MkScan _ d rest inv))
  (let-match many rest (Cons _ t more)
    ((Nil _)
      (match many d _
        ((Zero)
          (let ((erased acc)) (resume-accepts src d rest inv (AccEnd)))
          (values (Done Scan src (Accepted _ _ acc)) (StAccept src inv acc)))
        ((Succ k)
          (let ((erased bad)) (resume-fails src d rest inv (FailUnclosed k)))
          (values (Done Scan src (Rejected _ _ bad)) (StUnclosed src k inv bad))))))
  (let-match many t (Close)
    ((Open) (values (More Scan src (MkScan src (Succ d) more (ResOpen src d more inv))) (StOpen src d more inv))))
  (let-match many d (Succ k)
    ((Zero)
      (let ((erased bad)) (resume-fails src d rest inv (FailExtraClose more)))
      (values (Done Scan src (Rejected _ _ bad)) (StExtraClose src more inv bad))))
  (values (More Scan src (MkScan src k more (ResClose src k more inv))) (StClose src k more inv)))
