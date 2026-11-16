(let ((erased Store)) (List (Copy (Nat))))

(def-adts $ (HExpr : -> Type)
  enum
  (many HLit : (many (Nat) n) -> (HExpr))
  (many HGet : (many (HExpr) address) -> (HExpr))
  (many HSet : (many (HExpr) address) (many (HExpr) value) -> (HExpr))
  (many HPred : (many (HExpr) inner) -> (HExpr))
  (many HSeq : (many (HExpr) first) (many (HExpr) second) -> (HExpr))
  (many HWhile : (many (HExpr) condition) (many (HExpr) body) -> (HExpr)))

(def-adts
  ((PredOf : ((Nat) n) ((Nat) m) -> Type)
    enum
    (many PredZero : -> (PredOf (Zero) (Zero)))
    (many PredSucc : (erased (Nat) m) -> (PredOf (Succ m) m)))
  ((HEval : (Store before) ((HExpr) e) ((Nat) v) (Store after) -> Type)
    enum
    (many HvLit : (erased Store s) (erased (Nat) n) -> (HEval s (HLit n) n s))
    (many HvGet : (erased Store s) (erased (HExpr) address) (erased (Nat) a) (erased Store s1) (erased (Nat) v)
       (erased (HEval s address a s1) p) (erased (Nth (Copy (Nat)) s1 a (MkCopy (Nat) v)) holds) -> (HEval s (HGet address) v s1))
    (many HvSet : (erased Store s) (erased (HExpr) address) (erased (HExpr) value) (erased (Nat) a) (erased Store s1) (erased (Nat) v)
       (erased Store s2) (erased Store s3)
       (erased (HEval s address a s1) p) (erased (HEval s1 value v s2) q) (erased (SetNth (Copy (Nat)) s2 a (MkCopy (Nat) v) s3) written)
       -> (HEval s (HSet address value) v s3))
    (many HvPred : (erased Store s) (erased (HExpr) inner) (erased (Nat) n) (erased (Nat) m) (erased Store s1)
       (erased (HEval s inner n s1) p) (erased (PredOf n m) d) -> (HEval s (HPred inner) m s1))
    (many HvSeq : (erased Store s) (erased (HExpr) first) (erased (HExpr) second) (erased (Nat) v1) (erased Store s1) (erased (Nat) v2) (erased Store s2)
       (erased (HEval s first v1 s1) p) (erased (HEval s1 second v2 s2) q) -> (HEval s (HSeq first second) v2 s2))
    (many HvWhileDone : (erased Store s) (erased (HExpr) condition) (erased (HExpr) body) (erased Store s1)
       (erased (HEval s condition (Zero) s1) p) -> (HEval s (HWhile condition body) (Zero) s1))
    (many HvWhileStep : (erased Store s) (erased (HExpr) condition) (erased (HExpr) body) (erased (Nat) n) (erased Store s1) (erased (Nat) v)
       (erased Store s2) (erased (Nat) w) (erased Store s3)
       (erased (HEval s condition (Succ n) s1) p) (erased (HEval s1 body v s2) q) (erased (HEval s2 (HWhile condition body) w s3) r)
       -> (HEval s (HWhile condition body) w s3))))

(def-adts
  ((HTail : (Store s) ((HExpr) e) (Store s9) ((HExpr) e9) -> Type)
    enum
    (many HTailHere : (erased Store s) (erased (HExpr) e) -> (HTail s e s e))
    (many HTailSeq : (erased Store s9) (erased (HExpr) e9) (erased Store s) (erased (HExpr) first) (erased (HExpr) second) (erased (Nat) v1) (erased Store s1)
       (erased (HEval s first v1 s1) p) (erased (HTail s (HSeq first second) s9 e9) outer) -> (HTail s1 second s9 e9))
    (many HTailWhile : (erased Store s9) (erased (HExpr) e9) (erased Store s) (erased (HExpr) condition) (erased (HExpr) body) (erased (Nat) n)
       (erased Store s1) (erased (Nat) v) (erased Store s2)
       (erased (HEval s condition (Succ n) s1) p) (erased (HEval s1 body v s2) q) (erased (HTail s (HWhile condition body) s9 e9) outer)
       -> (HTail s2 (HWhile condition body) s9 e9))))

(def-fns _ $ (erased finish-htail : (erased Store s) (erased (HExpr) e) (erased Store s9) (erased (HExpr) e9) (erased (Nat) v) (erased Store after)
    (subterm erased (HTail s e s9 e9) t) (erased (HEval s e v after) p) -> (erased (HEval s9 e9 v after) q))
  (match erased t _
    ((HTailHere _ _) p)
    ((HTailSeq _ _ s0 first second v1 _ p1 outer) (finish-htail _ _ _ _ v after outer (HvSeq s0 first second v1 s v after p1 p)))
    ((HTailWhile _ _ s0 condition body n s1 v1 _ p1 q1 outer) (finish-htail _ _ _ _ v after outer (HvWhileStep s0 condition body n s1 v1 s v after p1 q1 p)))))

(def-adts
  ((HResume : (Store s) ((HExpr) e) (Store s0) ((HExpr) e0) -> Type)
    enum newtype
    (many MkHResume : (erased Store s0) (erased (HExpr) e0) (erased Store s) (erased (HExpr) e) (erased Store s9) (erased (HExpr) e9)
       (erased (HTail s e s9 e9) t) (many (HStack s9 e9 s0 e0) k) -> (HResume s e s0 e0)))
  ((HStack : (Store s) ((HExpr) e) (Store s0) ((HExpr) e0) -> Type)
    enum
    (many HDone : (erased Store s0) (erased (HExpr) e0) -> (HStack s0 e0 s0 e0))
    (many HKGet : (erased Store s0) (erased (HExpr) e0) (erased Store s) (erased (HExpr) address)
       (many (HResume s (HGet address) s0 e0) k) -> (HStack s address s0 e0))
    (many HKSetAddress : (erased Store s0) (erased (HExpr) e0) (erased Store s) (erased (HExpr) address) (many (HExpr) value)
       (many (HResume s (HSet address value) s0 e0) k) -> (HStack s address s0 e0))
    (many HKSetValue : (erased Store s0) (erased (HExpr) e0) (erased Store s) (erased (HExpr) address) (erased (HExpr) value) (many (Nat) a) (erased Store s1)
       (erased (HEval s address a s1) p)
       (many (HResume s (HSet address value) s0 e0) k) -> (HStack s1 value s0 e0))
    (many HKPred : (erased Store s0) (erased (HExpr) e0) (erased Store s) (erased (HExpr) inner)
       (many (HResume s (HPred inner) s0 e0) k) -> (HStack s inner s0 e0))
    (many HKSeq : (erased Store s0) (erased (HExpr) e0) (erased Store s) (erased (HExpr) first) (many (HExpr) second)
       (many (HResume s (HSeq first second) s0 e0) k) -> (HStack s first s0 e0))
    (many HKWhileCond : (erased Store s0) (erased (HExpr) e0) (erased Store s) (many (HExpr) condition) (many (HExpr) body)
       (many (HResume s (HWhile condition body) s0 e0) k) -> (HStack s condition s0 e0))
    (many HKWhileBody : (erased Store s0) (erased (HExpr) e0) (erased Store s) (many (HExpr) condition) (many (HExpr) body) (erased (Nat) n) (erased Store s1)
       (erased (HEval s condition (Succ n) s1) p)
       (many (HResume s (HWhile condition body) s0 e0) k) -> (HStack s1 body s0 e0))))

(def-adts
  ((HControl : (Store now) (Store s0) ((HExpr) e0) -> Type)
    enum
    (many HRun : (erased Store now) (erased Store s0) (erased (HExpr) e0) (many (HExpr) e) (many (HResume now e s0 e0) k) -> (HControl now s0 e0))
    (many HRet : (erased Store now) (erased Store s0) (erased (HExpr) e0) (erased Store s) (erased (HExpr) e) (many (Nat) v) (erased (HEval s e v now) p)
       (many (HResume s e s0 e0) k) -> (HControl now s0 e0)))
  ((HStepped : (Store now) (Store s0) ((HExpr) e0) -> Type)
    enum
    (many HNext : (erased Store now) (erased Store s0) (erased (HExpr) e0) (many (HControl now s0 e0) c) -> (HStepped now s0 e0))
    (many HHalted : (erased Store now) (erased Store s0) (erased (HExpr) e0) (many (Nat) v) (erased (HEval s0 e0 v now) p) -> (HStepped now s0 e0))
    (many HStuck : (erased Store now) (erased Store s0) (erased (HExpr) e0) -> (HStepped now s0 e0))))
