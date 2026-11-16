(def-adts
  ((Word : -> Type)
    enum
    (many WImm : (many (Nat) n) -> (Word))
    (many WAddr : (many (Nat) a) -> (Word)))
  ((Block : -> Type)
    enum
    (many MkBlock : (many (Nat) tag) (many (List (Word)) fields) -> (Block)))
  ((Heap : -> Type)
    enum
    (many HNil : -> (Heap))
    (many HCons : (many (Nat) a) (many (Block) b) (many (Heap) rest) -> (Heap))))

(def-adts
  ((Fresh : ((Heap) h) ((Nat) a) -> Type)
    enum
    (many FreshNil : (erased (Nat) a) -> (Fresh (HNil) a))
    (many FreshCons : (erased (Nat) a) (erased (Nat) b) (erased (Block) other) (erased (Heap) rest)
       (erased (Neq a b) n) (erased (Fresh rest a) p) -> (Fresh (HCons b other rest) a)))
  ((Lookup : ((Heap) h) ((Nat) a) ((Block) blk) -> Type)
    enum
    (many LkHere : (erased (Nat) a) (erased (Block) blk) (erased (Heap) rest) -> (Lookup (HCons a blk rest) a blk))
    (many LkThere : (erased (Nat) a) (erased (Nat) b) (erased (Block) blk) (erased (Block) other) (erased (Heap) rest)
       (erased (Neq a b) n) (erased (Lookup rest a blk) p) -> (Lookup (HCons b other rest) a blk)))
  ((Update : ((Heap) h) ((Nat) a) ((Block) blk) ((Heap) h2) -> Type)
    enum
    (many UpHere : (erased (Nat) a) (erased (Block) old) (erased (Block) blk) (erased (Heap) rest)
       -> (Update (HCons a old rest) a blk (HCons a blk rest)))
    (many UpThere : (erased (Nat) a) (erased (Nat) b) (erased (Block) blk) (erased (Block) other) (erased (Heap) rest) (erased (Heap) rest2)
       (erased (Neq a b) n) (erased (Update rest a blk rest2) p) -> (Update (HCons b other rest) a blk (HCons b other rest2))))
  ((Alloc : ((Heap) h) ((Nat) a) ((Block) blk) ((Heap) h2) -> Type)
    enum
    (many MkAlloc : (erased (Heap) h) (erased (Nat) a) (erased (Block) blk) (erased (Fresh h a) f) -> (Alloc h a blk (HCons a blk h)))))
