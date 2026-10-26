(def-adts $ (Sym : -> Type)
  enum
  (many Sym0 : -> (Sym))
  (many Sym1 : -> (Sym)))

(def-adts $ (Dir : -> Type)
  enum
  (many Left : -> (Dir))
  (many Right : -> (Dir)))

(def-adts $ (Entry : ((Nat) n) -> Type)
  enum
  (many Halt : (erased (Nat) n) -> (Entry n))
  (many Go : (erased (Nat) n) (many (Sym) w) (many (Dir) d) (many (Nat) q) (erased (Lt q n) below) -> (Entry n)))

(def-adts $ (Row : ((Nat) n) -> Type)
  enum
  (many MkRow : (erased (Nat) n) (many (Entry n) e0) (many (Entry n) e1) -> (Row n)))

(def-adts $ (Machine : ((Nat) n) -> Type)
  enum
  (many MkMachine : (erased (Nat) n) (many (List (Row n)) rows) (erased (Length (Row n) rows n) len) -> (Machine n)))

(def-adts $ (Lookup : ((Nat) n) ((Machine n) m) ((Nat) q) ((Sym) s) ((Entry n) e) -> Type)
  enum
  (many LookupSym0 : (erased (Nat) n) (erased (List (Row n)) rows) (erased (Length (Row n) rows n) len) (erased (Nat) q)
      (erased (Entry n) e0) (erased (Entry n) e1) (erased (Nth (Row n) rows q (MkRow n e0 e1)) nth)
      -> (Lookup n (MkMachine n rows len) q (Sym0) e0))
  (many LookupSym1 : (erased (Nat) n) (erased (List (Row n)) rows) (erased (Length (Row n) rows n) len) (erased (Nat) q)
      (erased (Entry n) e0) (erased (Entry n) e1) (erased (Nth (Row n) rows q (MkRow n e0 e1)) nth)
      -> (Lookup n (MkMachine n rows len) q (Sym1) e1)))

(def-adts $ (Cfg : -> Type)
  enum
  (many MkCfg : (many (Nat) q) (many (List (Sym)) ls) (many (Sym) h) (many (List (Sym)) rs) -> (Cfg)))

(def-adts $ (Pop : ((List (Sym)) xs) ((Sym) h) ((List (Sym)) rest) -> Type)
  enum
  (many PopNil : -> (Pop (Nil (Sym)) (Sym0) (Nil (Sym))))
  (many PopCons : (erased (Sym) x) (erased (List (Sym)) xs) -> (Pop (Cons (Sym) x xs) x xs)))

(def-adts $ (Step : ((Nat) n) ((Machine n) m) ((Cfg) c) ((Cfg) c2) -> Type)
  enum
  (many StepLeft : (erased (Nat) n) (erased (Machine n) m) (erased (Nat) q) (erased (List (Sym)) ls) (erased (Sym) h)
      (erased (List (Sym)) rs) (erased (Sym) w) (erased (Nat) q2) (erased (Lt q2 n) below)
      (erased (Lookup n m q h (Go n w (Left) q2 below)) look)
      (erased (Sym) h2) (erased (List (Sym)) ls2) (erased (Pop ls h2 ls2) pop)
      -> (Step n m (MkCfg q ls h rs) (MkCfg q2 ls2 h2 (Cons (Sym) w rs))))
  (many StepRight : (erased (Nat) n) (erased (Machine n) m) (erased (Nat) q) (erased (List (Sym)) ls) (erased (Sym) h)
      (erased (List (Sym)) rs) (erased (Sym) w) (erased (Nat) q2) (erased (Lt q2 n) below)
      (erased (Lookup n m q h (Go n w (Right) q2 below)) look)
      (erased (Sym) h2) (erased (List (Sym)) rs2) (erased (Pop rs h2 rs2) pop)
      -> (Step n m (MkCfg q ls h rs) (MkCfg q2 (Cons (Sym) w ls) h2 rs2))))

(def-adts $ (HaltsIn : ((Nat) n) ((Machine n) m) ((Cfg) c) ((Nat) k) -> Type)
  enum
  (many HaltNow : (erased (Nat) n) (erased (Machine n) m) (erased (Nat) q) (erased (List (Sym)) ls) (erased (Sym) h)
      (erased (List (Sym)) rs) (erased (Lookup n m q h (Halt n)) look)
      -> (HaltsIn n m (MkCfg q ls h rs) (Succ (Zero))))
  (many HaltLater : (erased (Nat) n) (erased (Machine n) m) (erased (Cfg) c) (erased (Cfg) c2) (erased (Step n m c c2) step)
      (erased (Nat) k) (erased (HaltsIn n m c2 k) rest) -> (HaltsIn n m c (Succ k))))

(let ((many blank)) (MkCfg (Zero) (Nil (Sym)) (Sym0) (Nil (Sym))))

(def-adts $ (BusyBeaver : ((Nat) n) ((Nat) v) -> Type)
  enum
  (many MkBusyBeaver : (erased (Nat) n) (erased (Nat) v)
      (erased (Machine n) champion) (erased (HaltsIn n champion blank v) halts)
      (erased (Level) L)
      (erased (Fn L (erased (Machine n) m) (erased (Nat) k) (erased (HaltsIn n m blank k) h) ->
          (erased (Le k v) le)) bound)
      -> (BusyBeaver n v)))
