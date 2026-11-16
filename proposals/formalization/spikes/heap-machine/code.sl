(def-adts
  ((Atom : -> Type)
    enum
    (many AVar : (many (Nat) i) -> (Atom))
    (many AImm : (many (Nat) n) -> (Atom)))
  ((Instr : -> Type)
    enum
    (many IAtom : (many (Atom) a) -> (Instr))
    (many ICon : (many (Nat) tag) (many (List (Atom)) args) -> (Instr))
    (many IWrite : (many (Atom) target) (many (Nat) i) (many (Atom) v) -> (Instr))
    (many ICopy : (many (Atom) target) (many (Nat) i) (many (Atom) v) -> (Instr))
    (many ISame : (many (Atom) a) (many (Atom) b) -> (Instr)))
  ((Code : -> Type)
    enum
    (many CDo : (many (Instr) i) -> (Code))
    (many CLet : (many (Code) rhs) (many (Code) body) -> (Code))
    (many CMatch : (many (Atom) scrut) (many (List (Code)) blocks) (many (List (Code)) imms) -> (Code))
    (many CCall : (many (Nat) f) (many (List (Atom)) args) -> (Code)))
  ((Label : -> Type)
    enum
    (many LTau : -> (Label))
    (many LAddr : (many (Nat) a) -> (Label))
    (many LYes : -> (Label))
    (many LNo : -> (Label))))

(def-adts
  ((AtomVal : ((List (Word)) env) ((Atom) a) ((Word) w) -> Type)
    enum
    (many AVVar : (erased (List (Word)) env) (erased (Nat) i) (erased (Word) w) (erased (Nth (Word) env i w) p) -> (AtomVal env (AVar i) w))
    (many AVImm : (erased (List (Word)) env) (erased (Nat) n) -> (AtomVal env (AImm n) (WImm n))))
  ((AtomVals : ((List (Word)) env) ((List (Atom)) as) ((List (Word)) ws) -> Type)
    enum
    (many AVsNil : (erased (List (Word)) env) -> (AtomVals env (Nil (Atom)) (Nil (Word))))
    (many AVsCons : (erased (List (Word)) env) (erased (Atom) a) (erased (Word) w) (erased (List (Atom)) as) (erased (List (Word)) ws)
       (erased (AtomVal env a w) p) (erased (AtomVals env as ws) q) -> (AtomVals env (Cons (Atom) a as) (Cons (Word) w ws))))
  ((Cat : ((List (Word)) xs) ((List (Word)) ys) ((List (Word)) zs) -> Type)
    enum
    (many CatNil : (erased (List (Word)) ys) -> (Cat (Nil (Word)) ys ys))
    (many CatCons : (erased (Word) x) (erased (List (Word)) xs) (erased (List (Word)) ys) (erased (List (Word)) zs)
       (erased (Cat xs ys zs) p) -> (Cat (Cons (Word) x xs) ys (Cons (Word) x zs)))))

(def-adts
  ((Patched : ((Heap) h) ((List (Word)) env) ((Atom) a) ((Nat) i) ((Atom) b) ((Nat) p) ((Block) blk) -> Type)
    enum
    (many MkPatched : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
       (erased (Nat) p) (erased (Word) w) (erased (Nat) tag) (erased (List (Word)) fs) (erased (List (Word)) fs2)
       (erased (AtomVal env a (WAddr p)) pa) (erased (AtomVal env b w) pb) (erased (Lookup h p (MkBlock tag fs)) lk)
       (erased (SetNth (Word) fs i w fs2) st) -> (Patched h env a i b p (MkBlock tag fs2))))
  ((Prim : ((Heap) h) ((List (Word)) env) ((Instr) i) ((Label) l) ((Heap) h2) ((Word) w) -> Type)
    enum
    (many PAtom : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Word) w)
       (erased (AtomVal env a w) p) -> (Prim h env (IAtom a) (LTau) h w))
    (many PCon : (erased (Heap) h) (erased (List (Word)) env) (erased (Nat) tag) (erased (List (Atom)) args)
       (erased (List (Word)) ws) (erased (Nat) p) (erased (Heap) h2)
       (erased (AtomVals env args ws) pa) (erased (Alloc h p (MkBlock tag ws) h2) al) -> (Prim h env (ICon tag args) (LAddr p) h2 (WAddr p)))
    (many PWrite : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
       (erased (Nat) p) (erased (Block) blk) (erased (Heap) h2)
       (erased (Patched h env a i b p blk) pt) (erased (Update h p blk h2) up) -> (Prim h env (IWrite a i b) (LTau) h2 (WAddr p)))
    (many PCopy : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
       (erased (Nat) p) (erased (Block) blk) (erased (Nat) q) (erased (Heap) h2)
       (erased (Patched h env a i b p blk) pt) (erased (Alloc h q blk h2) al) -> (Prim h env (ICopy a i b) (LAddr q) h2 (WAddr q)))
    (many PSameYes : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Atom) b) (erased (Word) w)
       (erased (AtomVal env a w) pa) (erased (AtomVal env b w) pb) -> (Prim h env (ISame a b) (LYes) h (WImm (Succ (Zero)))))
    (many PSameNo : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Atom) b) (erased (Word) w1) (erased (Word) w2)
       (erased (AtomVal env a w1) pa) (erased (AtomVal env b w2) pb) -> (Prim h env (ISame a b) (LNo) h (WImm (Zero)))))
  ((Select : ((Heap) h) ((Word) w) ((List (Code)) blocks) ((List (Code)) imms) ((Code) body) ((List (Word)) fields) -> Type)
    enum
    (many SelImm : (erased (Heap) h) (erased (Nat) n) (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Code) body)
       (erased (Nth (Code) imms n body) br) -> (Select h (WImm n) blocks imms body (Nil (Word))))
    (many SelBlock : (erased (Heap) h) (erased (Nat) p) (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Code) body)
       (erased (Nat) tag) (erased (List (Word)) fs)
       (erased (Lookup h p (MkBlock tag fs)) lk) (erased (Nth (Code) blocks tag body) br) -> (Select h (WAddr p) blocks imms body fs))))
