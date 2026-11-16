(def-adts
  ((Why : -> Type)
    enum
    (many NoVar : -> (Why))
    (many NoFn : -> (Why))
    (many Dangling : -> (Why))
    (many NotBlock : -> (Why))
    (many NoField : -> (Why))
    (many NoBranch : -> (Why)))
  ((Halt : -> Type)
    enum
    (many OutOfFuel : -> (Halt))
    (many Stuck : (many (Why) why) -> (Halt))))

(def-adts
  ((AtomValDec : ((List (Word)) env) ((Atom) a) -> Type)
    enum
    (many AVHit : (erased (List (Word)) env) (erased (Atom) a) (many (Word) w) (erased (AtomVal env a w) p) -> (AtomValDec env a))
    (many AVMiss : (erased (List (Word)) env) (erased (Atom) a) -> (AtomValDec env a)))
  ((AtomValsDec : ((List (Word)) env) ((List (Atom)) as) -> Type)
    enum
    (many AVsHit : (erased (List (Word)) env) (erased (List (Atom)) as) (many (List (Word)) ws) (erased (AtomVals env as ws) p) -> (AtomValsDec env as))
    (many AVsMiss : (erased (List (Word)) env) (erased (List (Atom)) as) -> (AtomValsDec env as)))
  ((SetNthDec : (Type A) ((List A) xs) ((Nat) i) (A y) -> Type)
    enum
    (many SetHit : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A y) (many (List A) ys) (erased (SetNth A xs i y ys) p) -> (SetNthDec A xs i y))
    (many SetMiss : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A y) -> (SetNthDec A xs i y)))
  ((PatchedDec : ((Heap) h) ((List (Word)) env) ((Atom) a) ((Nat) i) ((Atom) b) -> Type)
    enum
    (many PaHit : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
       (many (Nat) p) (many (Block) blk) (erased (Patched h env a i b p blk) d) -> (PatchedDec h env a i b))
    (many PaMiss : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a) (erased (Nat) i) (erased (Atom) b) (many (Why) why) -> (PatchedDec h env a i b)))
  ((WordDec : ((Word) a) ((Word) b) -> Type)
    enum
    (many WSame : (erased (Word) a) -> (WordDec a a))
    (many WDiff : (erased (Word) a) (erased (Word) b) -> (WordDec a b)))
  ((SelectDec : ((Heap) h) ((Word) w) ((List (Code)) blocks) ((List (Code)) imms) -> Type)
    enum
    (many SelHit : (erased (Heap) h) (erased (Word) w) (erased (List (Code)) blocks) (erased (List (Code)) imms)
       (many (Code) body) (many (List (Word)) fs) (erased (Select h w blocks imms body fs) d) -> (SelectDec h w blocks imms))
    (many SelMiss : (erased (Heap) h) (erased (Word) w) (erased (List (Code)) blocks) (erased (List (Code)) imms) (many (Why) why) -> (SelectDec h w blocks imms)))
  ((Primmed : ((Heap) h) ((List (Word)) env) ((Instr) i) -> Type)
    enum
    (many PrimOk : (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i)
       (many (Heap) h2) (many (Nat) next2) (erased (Below h2 next2) inv2) (many (Word) w)
       (erased (Label) l) (erased (Prim h env i l h2 w) d) -> (Primmed h env i))
    (many PrimStuck : (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i) (many (Why) why) -> (Primmed h env i))))

(def-fns _ $ (many atom-val : (many (List (Word)) env) (many (Atom) a) -> (many (AtomValDec env a) r))
  (let-match many a (AVar i) ((AImm n) (AVHit _ _ (WImm n) $ AVImm env n)))
  (match many (nth-dec _ env i) _
    ((NthHit _ _ _ w p) (AVHit _ _ w $ AVVar env i w p))
    ((NthMiss _ _ _ _) (AVMiss _ _))))

(def-fns _ $ (many atom-vals : (many (List (Word)) env) (subterm many (List (Atom)) as) -> (many (AtomValsDec env as) r))
  (let-match many as (Cons _ a rest) ((Nil _) (AVsHit _ _ (Nil _) $ AVsNil env)))
  (let-match many (atom-val env a) (AVHit _ _ w p) ((AVMiss _ _) (AVsMiss _ _)))
  (match many (notail $ atom-vals env rest) _
    ((AVsMiss _ _) (AVsMiss _ _))
    ((AVsHit _ _ ws q) (AVsHit _ _ (Cons _ w ws) $ AVsCons env a w rest ws p q))))

(def-fns _ $ (many cat : (subterm many (List (Word)) xs) (many (List (Word)) ys) -> (many (List (Word)) zs) (erased (Cat xs ys zs) p))
  (let-match many xs (Cons _ x rest) ((Nil _) (values ys (CatNil ys))))
  (let ((many zs) (erased p)) (notail $ cat rest ys))
  (values (Cons _ x zs) (CatCons x rest ys zs p)))

(def-fns _ $ (many setnth-dec : (erased Type A) (subterm many (List A) xs) (many (Nat) i) (many A y) -> (many (SetNthDec A xs i y) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (SetMiss _ _ _ _)))
  (let-match many i (Succ j) ((Zero) (SetHit _ _ _ _ (Cons _ y rest) $ SetHere _ x y rest)))
  (match many (notail $ setnth-dec _ rest j y) _
    ((SetMiss _ _ _ _) (SetMiss _ _ _ _))
    ((SetHit _ _ _ _ ys p) (SetHit _ _ _ _ (Cons _ x ys) $ SetThere _ x rest j y ys p))))

(def-fns _ $ (many patched : (many (Heap) h) (many (List (Word)) env) (many (Atom) a) (many (Nat) i) (many (Atom) b) -> (many (PatchedDec h env a i b) r))
  (let-match many (atom-val env a) (AVHit _ _ wa pa) ((AVMiss _ _) (PaMiss _ _ _ _ _ (NoVar))))
  (let-match many (atom-val env b) (AVHit _ _ w pb) ((AVMiss _ _) (PaMiss _ _ _ _ _ (NoVar))))
  (let-match many wa (WAddr p) ((WImm _) (PaMiss _ _ _ _ _ (NotBlock))))
  (let-match many (lookup-dec h p) (LkHit _ _ blk lk) ((LkMiss _ _ _) (PaMiss _ _ _ _ _ (Dangling))))
  (let-match many blk (MkBlock tag fs))
  (match many (setnth-dec _ fs i w) _
    ((SetMiss _ _ _ _) (PaMiss _ _ _ _ _ (NoField)))
    ((SetHit _ _ _ _ fs2 st) (PaHit _ _ _ _ _ p (MkBlock tag fs2) $ MkPatched h env a i b p w tag fs fs2 pa pb lk st))))

(def-fns _ $ (many word-dec : (many (Word) a) (many (Word) b) -> (many (WordDec a b) r))
  (match many a _
    ((WImm n)
      (let-match many b (WImm m) ((WAddr _) (WDiff _ _)))
      (match many (nat-dec n m) _ ((NDSame _) (WSame _)) ((NDDiff _ _ _) (WDiff _ _))))
    ((WAddr p)
      (let-match many b (WAddr q) ((WImm _) (WDiff _ _)))
      (match many (nat-dec p q) _ ((NDSame _) (WSame _)) ((NDDiff _ _ _) (WDiff _ _))))))

(def-fns _ $ (many select : (many (Heap) h) (many (Word) w) (many (List (Code)) blocks) (many (List (Code)) imms) -> (many (SelectDec h w blocks imms) r))
  (match many w _
    ((WImm n)
      (match many (nth-dec _ imms n) _
        ((NthMiss _ _ _ _) (SelMiss _ _ _ _ (NoBranch)))
        ((NthHit _ _ _ body br) (SelHit _ _ _ _ body (Nil _) $ SelImm h n blocks imms body br))))
    ((WAddr p)
      (let-match many (lookup-dec h p) (LkHit _ _ blk lk) ((LkMiss _ _ _) (SelMiss _ _ _ _ (Dangling))))
      (let-match many blk (MkBlock tag fs))
      (match many (nth-dec _ blocks tag) _
        ((NthMiss _ _ _ _) (SelMiss _ _ _ _ (NoBranch)))
        ((NthHit _ _ _ body br) (SelHit _ _ _ _ body fs $ SelBlock h p blocks imms body tag fs lk br))))))

(def-fns _ $ (many prim : (many (Heap) h) (many (Nat) next) (erased (Below h next) inv) (many (List (Word)) env) (many (Instr) i) -> (many (Primmed h env i) r))
  (match many i _
    ((IAtom a)
      (match many (atom-val env a) _
        ((AVMiss _ _) (PrimStuck _ _ _ (NoVar)))
        ((AVHit _ _ w p) (PrimOk _ _ _ h next inv w (LTau) $ PAtom h env a w p))))
    ((ICon tag args)
      (let-match many (atom-vals env args) (AVsHit _ _ ws pa) ((AVsMiss _ _) (PrimStuck _ _ _ (NoVar))))
      (let ((many h2) (many next2) (erased inv2) (erased al)) (alloc h next inv (MkBlock tag ws)))
      (PrimOk _ _ _ h2 next2 inv2 (WAddr next) (LAddr next) $ PCon h env tag args ws next h2 pa al))
    ((IWrite a j b)
      (let-match many (patched h env a j b) (PaHit _ _ _ _ _ p blk pt) ((PaMiss _ _ _ _ _ why) (PrimStuck _ _ _ why)))
      (let-match erased pt (MkPatched _ _ _ _ _ _ _ tag fs _ _ _ lk _))
      (let ((many h2) (erased up)) (update h p blk (MkBlock tag fs) lk))
      (PrimOk _ _ _ h2 next (below-update h next p blk h2 inv up) (WAddr p) (LTau) $ PWrite h env a j b p blk h2 pt up))
    ((ICopy a j b)
      (let-match many (patched h env a j b) (PaHit _ _ _ _ _ p blk pt) ((PaMiss _ _ _ _ _ why) (PrimStuck _ _ _ why)))
      (let ((many h2) (many next2) (erased inv2) (erased al)) (alloc h next inv blk))
      (PrimOk _ _ _ h2 next2 inv2 (WAddr next) (LAddr next) $ PCopy h env a j b p blk next h2 pt al))
    ((ISame a b)
      (let-match many (atom-val env a) (AVHit _ _ wa pa) ((AVMiss _ _) (PrimStuck _ _ _ (NoVar))))
      (let-match many (atom-val env b) (AVHit _ _ wb pb) ((AVMiss _ _) (PrimStuck _ _ _ (NoVar))))
      (match many (word-dec wa wb) _
        ((WSame _) (PrimOk _ _ _ h next inv (WImm (Succ (Zero))) (LYes) $ PSameYes h env a b wa pa pb))
        ((WDiff _ _) (PrimOk _ _ _ h next inv (WImm (Zero)) (LNo) $ PSameNo h env a b wa wb pa pb))))))
