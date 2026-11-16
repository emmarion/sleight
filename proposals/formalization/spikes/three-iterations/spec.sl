(def-adts $ (Tok : -> Type)
  enum
  (many Open : -> (Tok))
  (many Close : -> (Tok)))

(def-adts $ (Accepts : ((Nat) depth) ((List (Tok)) src) -> Type)
  enum
  (many AccEnd : -> (Accepts (Zero) (Nil (Tok))))
  (many AccOpen : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Accepts (Succ d) ts) p) -> (Accepts d (Cons (Tok) (Open) ts)))
  (many AccClose : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Accepts d ts) p) -> (Accepts (Succ d) (Cons (Tok) (Close) ts))))

(def-adts $ (Fails : ((Nat) depth) ((List (Tok)) src) -> Type)
  enum
  (many FailUnclosed : (erased (Nat) d) -> (Fails (Succ d) (Nil (Tok))))
  (many FailExtraClose : (erased (List (Tok)) ts) -> (Fails (Zero) (Cons (Tok) (Close) ts)))
  (many FailOpen : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Fails (Succ d) ts) p) -> (Fails d (Cons (Tok) (Open) ts)))
  (many FailClose : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Fails d ts) p) -> (Fails (Succ d) (Cons (Tok) (Close) ts))))

(def-adts $ (Verdict : ((Nat) depth) ((List (Tok)) src) -> Type)
  enum
  (many Accepted : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Accepts d ts) p) -> (Verdict d ts))
  (many Rejected : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Fails d ts) p) -> (Verdict d ts)))

(def-adts $ (Stepped : ((TyCtor ((List (Tok)) src) -> Type) State) ((List (Tok)) src) -> Type)
  enum
  (many More : (erased (TyCtor ((List (Tok)) src) -> Type) State) (erased (List (Tok)) src) (many (State src) next) -> (Stepped State src))
  (many Done : (erased (TyCtor ((List (Tok)) src) -> Type) State) (erased (List (Tok)) src) (many (Verdict (Zero) src) v) -> (Stepped State src)))

(def-adts $ (CertifiedOnExit : -> Type)
  enum
  (many MkCertifiedOnExit : (erased (TyCtor ((List (Tok)) src) -> Type) State) (erased (Level) L)
     (many (Fn L (many (List (Tok)) src) -> (many (State src) s)) start)
     (many (Fn L (erased (List (Tok)) src) (many (State src) s) -> (many (Stepped State src) r)) step)
     -> (CertifiedOnExit)))

