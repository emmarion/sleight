; mini/ctx.sl -- the scope environment and fact table of DESIGN.md sections 3 and 18 for the minimal
; language: entries with a type and a kind, names, the declared ADTs, and the rules of mini/canon.sl, in one
; record with the ambient level and subterm arguments. Lookups come with evidence. One session's proposal.

; An entry's kind: [KDecl] is a type or value constructor declared by def-adts or built in, rigid for
; unification (ASSUMPTIONS 40); [KLevel] an entry def-lvl minted (section 8's marker).
(def-adts
  (Kind : -> Type
    enum
    (many KPlain : -> (Kind))
    (many KLevel : -> (Kind))
    (many KDecl : -> (Kind)))
  (Ent : -> Type
    enum
    (many MkEnt : (many (Nat) id) (many (Term) ty) (many (Kind) kind) -> (Ent)))
  (Name : -> Type
    enum
    (many MkName : (many (String) name) (many (Nat) id) -> (Name)))
  (Adt : -> Type
    enum
    (many MkAdt : (many (Nat) tycon) (many (List (Nat)) ctors) -> (Adt)))
  ; [next] is the first unused id: ids are never reused, so leaving a scope restores the lists and keeps it.
  ; [level] is the current function's level, or [None] at the top level (section 24); [subargs] the
  ; enclosing function's subterm-marked parameters (section 3).
  (Ctx : -> Type
    enum
    (many MkCtx : (many (Nat) next) (many (List (Name)) scope) (many (List (Ent)) ents) (many (List (Rule)) rules) (many (List (Adt)) adts)
       (many (Maybe (Term)) level) (many (List (Term)) subargs) -> (Ctx))))

(def-adts
  (EntOf : ((List (Ent)) ents) ((Nat) x) ((Term) ty) ((Kind) k) -> Type
    enum
    (many EntHere : (erased (Nat) x) (erased (Term) ty) (erased (Kind) k) (erased (List (Ent)) rest) -> (EntOf (Cons (Ent) (MkEnt x ty k) rest) x ty k))
    (many EntThere : (erased (Nat) x) (erased (Nat) y) (erased (Term) ty) (erased (Term) ty2) (erased (Kind) k) (erased (Kind) k2) (erased (List (Ent)) rest)
       (erased (Neq x y) n) (erased (EntOf rest x ty k) p) -> (EntOf (Cons (Ent) (MkEnt y ty2 k2) rest) x ty k)))
  (NoEnt : ((List (Ent)) ents) ((Nat) x) -> Type
    enum
    (many NoEntNil : (erased (Nat) x) -> (NoEnt (Nil (Ent)) x))
    (many NoEntCons : (erased (Nat) x) (erased (Nat) y) (erased (Term) ty2) (erased (Kind) k2) (erased (List (Ent)) rest) (erased (Neq x y) n) (erased (NoEnt rest x) p) ->
       (NoEnt (Cons (Ent) (MkEnt y ty2 k2) rest) x)))
  (EntDec : ((List (Ent)) ents) ((Nat) x) -> Type
    enum
    (many EntHit : (erased (List (Ent)) ents) (erased (Nat) x) (many (Term) ty) (many (Kind) k) (erased (EntOf ents x ty k) p) -> (EntDec ents x))
    (many EntMiss : (erased (List (Ent)) ents) (erased (Nat) x) (erased (NoEnt ents x) p) -> (EntDec ents x))))

(def-fns _ $ many ent-dec : (subterm many (List (Ent)) ents) (many (Nat) x) -> (many (EntDec ents x) r)
  (match many ents _
    ((Nil a) (EntMiss _ _ $ NoEntNil x))
    ((Cons a e rest)
      (match many e _
        ((MkEnt y ty2 k2)
          (match many (nat-dec x y) _
            ((NDSame z) (EntHit _ _ ty2 k2 $ EntHere x ty2 k2 rest))
            ((NDDiff z w n)
              (match many (ent-dec rest x) _
                ((EntHit l z2 ty k p) (EntHit _ _ ty k $ EntThere x y ty ty2 k k2 rest n p))
                ((EntMiss l z2 p) (EntMiss _ _ $ NoEntCons x y ty2 k2 rest n p))))))))))

(def-adts
  (StrNeq : ((String) a) ((String) b) -> Type
    enum
    (many StrNeqLt : (erased (String) a) (erased (String) b) (erased (StrLt a b) p) -> (StrNeq a b))
    (many StrNeqGt : (erased (String) a) (erased (String) b) (erased (StrLt b a) p) -> (StrNeq a b)))
  (NameOf : ((List (Name)) scope) ((String) s) ((Nat) x) -> Type
    enum
    (many NameHere : (erased (String) s) (erased (Nat) x) (erased (List (Name)) rest) -> (NameOf (Cons (Name) (MkName s x) rest) s x))
    (many NameThere : (erased (String) s) (erased (String) s2) (erased (Nat) x) (erased (Nat) y) (erased (List (Name)) rest) (erased (StrNeq s s2) n) (erased (NameOf rest s x) p) ->
       (NameOf (Cons (Name) (MkName s2 y) rest) s x)))
  (NoName : ((List (Name)) scope) ((String) s) -> Type
    enum
    (many NoNameNil : (erased (String) s) -> (NoName (Nil (Name)) s))
    (many NoNameCons : (erased (String) s) (erased (String) s2) (erased (Nat) y) (erased (List (Name)) rest) (erased (StrNeq s s2) n) (erased (NoName rest s) p) ->
       (NoName (Cons (Name) (MkName s2 y) rest) s)))
  (NameDec : ((List (Name)) scope) ((String) s) -> Type
    enum
    (many NameHit : (erased (List (Name)) scope) (erased (String) s) (many (Nat) x) (erased (NameOf scope s x) p) -> (NameDec scope s))
    (many NameMiss : (erased (List (Name)) scope) (erased (String) s) (erased (NoName scope s) p) -> (NameDec scope s))))

(def-fns _ $ many name-dec : (subterm many (List (Name)) scope) (many (String) s) -> (many (NameDec scope s) r)
  (match many scope _
    ((Nil a) (NameMiss _ _ $ NoNameNil s))
    ((Cons a e rest)
      (match many e _
        ((MkName s2 y)
          (match many (str-cmp s s2) _
            ((CEq t r z) (NameHit _ _ y $ NameHere s y rest))
            ((CLt t r z w p)
              (match many (name-dec rest s) _
                ((NameHit l z2 x q) (NameHit _ _ x $ NameThere s s2 x y rest (StrNeqLt s s2 p) q))
                ((NameMiss l z2 q) (NameMiss _ _ $ NoNameCons s s2 y rest (StrNeqLt s s2 p) q))))
            ((CGt t r z w p)
              (match many (name-dec rest s) _
                ((NameHit l z2 x q) (NameHit _ _ x $ NameThere s s2 x y rest (StrNeqGt s s2 p) q))
                ((NameMiss l z2 q) (NameMiss _ _ $ NoNameCons s s2 y rest (StrNeqGt s s2 p) q))))))))))

; The constructors a declared type constructor has, or evidence that none was declared, which is what
; makes a type unmatchable (MINIMAL.md's rule for match).
(def-adts
  (AdtOf : ((List (Adt)) adts) ((Nat) t) ((List (Nat)) ctors) -> Type
    enum
    (many AdtHere : (erased (Nat) t) (erased (List (Nat)) ctors) (erased (List (Adt)) rest) -> (AdtOf (Cons (Adt) (MkAdt t ctors) rest) t ctors))
    (many AdtThere : (erased (Nat) t) (erased (Nat) t2) (erased (List (Nat)) ctors) (erased (List (Nat)) ctors2) (erased (List (Adt)) rest) (erased (Neq t t2) n) (erased (AdtOf rest t ctors) p) ->
       (AdtOf (Cons (Adt) (MkAdt t2 ctors2) rest) t ctors)))
  (NoAdt : ((List (Adt)) adts) ((Nat) t) -> Type
    enum
    (many NoAdtNil : (erased (Nat) t) -> (NoAdt (Nil (Adt)) t))
    (many NoAdtCons : (erased (Nat) t) (erased (Nat) t2) (erased (List (Nat)) ctors2) (erased (List (Adt)) rest) (erased (Neq t t2) n) (erased (NoAdt rest t) p) ->
       (NoAdt (Cons (Adt) (MkAdt t2 ctors2) rest) t)))
  (AdtDec : ((List (Adt)) adts) ((Nat) t) -> Type
    enum
    (many AdtHit : (erased (List (Adt)) adts) (erased (Nat) t) (many (List (Nat)) ctors) (erased (AdtOf adts t ctors) p) -> (AdtDec adts t))
    (many AdtMiss : (erased (List (Adt)) adts) (erased (Nat) t) (erased (NoAdt adts t) p) -> (AdtDec adts t))))

(def-fns _ $ many adt-dec : (subterm many (List (Adt)) adts) (many (Nat) t) -> (many (AdtDec adts t) r)
  (match many adts _
    ((Nil a) (AdtMiss _ _ $ NoAdtNil t))
    ((Cons a e rest)
      (match many e _
        ((MkAdt t2 ctors2)
          (match many (nat-dec t t2) _
            ((NDSame z) (AdtHit _ _ ctors2 $ AdtHere t ctors2 rest))
            ((NDDiff z w n)
              (match many (adt-dec rest t) _
                ((AdtHit l z2 ctors p) (AdtHit _ _ ctors $ AdtThere t t2 ctors ctors2 rest n p))
                ((AdtMiss l z2 p) (AdtMiss _ _ $ NoAdtCons t t2 ctors2 rest n p))))))))))

(MkUnit)
