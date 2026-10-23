(def-adts
  ((Folded : ((Char) c) ((Nat) k) -> Type)
    enum
    (many FoldUpper : (erased (Nat) n) (erased (Lt n u8-modulus) p) (erased (Lt 64 n) above-at) (erased (Lt n 91) below-bracket)
       (erased (Nat) k) (erased (Add n 32 k) shift) -> (Folded (MkChar (MkU8 n p)) k))
    (many FoldBelow : (erased (Nat) n) (erased (Lt n u8-modulus) p) (erased (Lt n 65) below-a) -> (Folded (MkChar (MkU8 n p)) n))
    (many FoldAbove : (erased (Nat) n) (erased (Lt n u8-modulus) p) (erased (Lt 90 n) above-z) -> (Folded (MkChar (MkU8 n p)) n))))

(def-adts
  ((SameLetter : ((Char) x) ((Char) y) -> Type)
    enum
    (many Same : (erased (Char) x) (erased (Char) y) (erased (Nat) k) (erased (Folded x k) fx) (erased (Folded y k) fy)
       -> (SameLetter x y))))

(def-adts
  ((DifferentLetter : ((Char) x) ((Char) y) -> Type)
    enum
    (many Below : (erased (Char) x) (erased (Char) y) (erased (Nat) i) (erased (Nat) j) (erased (Folded x i) fx) (erased (Folded y j) fy)
       (erased (Lt i j) lt) -> (DifferentLetter x y))
    (many Above : (erased (Char) x) (erased (Char) y) (erased (Nat) i) (erased (Nat) j) (erased (Folded x i) fx) (erased (Folded y j) fy)
       (erased (Lt j i) gt) -> (DifferentLetter x y))))

(def-adts
  ((Edits : ((String) a) ((String) b) ((Nat) n) -> Type)
    enum
    (many Done : -> (Edits (SNil) (SNil) (Zero)))
    (many Keep : (erased (Char) x) (erased (Char) y) (erased (String) a) (erased (String) b) (erased (Nat) n)
       (erased (SameLetter x y) same) (erased (Edits a b n) rest) -> (Edits (SCons x a) (SCons y b) n))
    (many Replace : (erased (Char) x) (erased (Char) y) (erased (String) a) (erased (String) b) (erased (Nat) n)
       (erased (Edits a b n) rest) -> (Edits (SCons x a) (SCons y b) (Succ n)))
    (many Delete : (erased (Char) x) (erased (String) a) (erased (String) b) (erased (Nat) n)
       (erased (Edits a b n) rest) -> (Edits (SCons x a) b (Succ n)))
    (many Insert : (erased (Char) y) (erased (String) a) (erased (String) b) (erased (Nat) n)
       (erased (Edits a b n) rest) -> (Edits a (SCons y b) (Succ n)))
    (many Swap : (erased (Char) x1) (erased (Char) x2) (erased (Char) y1) (erased (Char) y2) (erased (String) a) (erased (String) b) (erased (Nat) n)
       (erased (SameLetter x1 y2) first) (erased (SameLetter x2 y1) second) (erased (Edits a b n) rest)
       -> (Edits (SCons x1 (SCons x2 a)) (SCons y1 (SCons y2 b)) (Succ n)))))

(def-adts
  ((LetterCost : ((Char) x) ((Char) y) ((Nat) c) -> Type)
    enum
    (many LettersMatch : (erased (Char) x) (erased (Char) y) (erased (SameLetter x y) same) -> (LetterCost x y (Zero)))
    (many LettersDiffer : (erased (Char) x) (erased (Char) y) (erased (DifferentLetter x y) differ) -> (LetterCost x y (Succ (Zero))))))

(def-adts
  ((Covers : ((Nat) c) ((Nat) j) ((Nat) k) -> Type)
    enum
    (many MkCovers : (erased (Nat) c) (erased (Nat) j) (erased (Nat) k) (erased (Nat) s) (erased (Add c j s) total) (erased (Le k s) enough)
       -> (Covers c j k))))

(def-adts
  ((AtLeast : ((String) a) ((String) b) ((Nat) k) -> Type)
    enum
    (many Trivially : (erased (String) a) (erased (String) b) -> (AtLeast a b (Zero)))
    (many OnlyDeletes : (erased (Char) x) (erased (String) a) (erased (Nat) k) (erased (Nat) j)
       (erased (AtLeast a (SNil) j) rest) (erased (Covers (Succ (Zero)) j k) enough) -> (AtLeast (SCons x a) (SNil) k))
    (many OnlyInserts : (erased (Char) y) (erased (String) b) (erased (Nat) k) (erased (Nat) j)
       (erased (AtLeast (SNil) b j) rest) (erased (Covers (Succ (Zero)) j k) enough) -> (AtLeast (SNil) (SCons y b) k))
    (many EveryFirstStep : (erased (Char) x) (erased (Char) y) (erased (String) a) (erased (String) b) (erased (Nat) k)
       (erased (Nat) cp) (erased (LetterCost x y cp) pair-cost) (erased (Nat) jp) (erased (AtLeast a b jp) pair) (erased (Covers cp jp k) pair-enough)
       (erased (Nat) jd) (erased (AtLeast a (SCons y b) jd) delete) (erased (Covers (Succ (Zero)) jd k) delete-enough)
       (erased (Nat) ji) (erased (AtLeast (SCons x a) b ji) insert) (erased (Covers (Succ (Zero)) ji k) insert-enough)
       (erased (SwapBound x a y b k) swap)
       -> (AtLeast (SCons x a) (SCons y b) k)))
  ((SwapBound : ((Char) x) ((String) a) ((Char) y) ((String) b) ((Nat) k) -> Type)
    enum
    (many NothingToSwapLeft : (erased (Char) x) (erased (Char) y) (erased (String) b) (erased (Nat) k)
       -> (SwapBound x (SNil) y b k))
    (many NothingToSwapRight : (erased (Char) x) (erased (String) a) (erased (Char) y) (erased (Nat) k)
       -> (SwapBound x a y (SNil) k))
    (many SwapCosts : (erased (Char) x1) (erased (Char) x2) (erased (String) a) (erased (Char) y1) (erased (Char) y2) (erased (String) b) (erased (Nat) k)
       (erased (Nat) c1) (erased (LetterCost x1 y2 c1) first-cost) (erased (Nat) c2) (erased (LetterCost x2 y1 c2) second-cost)
       (erased (Nat) c) (erased (Add c1 c2 c) mismatches) (erased (Nat) j) (erased (AtLeast a b j) rest) (erased (Covers (Succ c) j k) enough)
       -> (SwapBound x1 (SCons x2 a) y1 (SCons y2 b) k))))

(def-adts
  ((Distance : ((String) a) ((String) b) ((Nat) n) -> Type)
    enum
    (many MkDistance : (erased (String) a) (erased (String) b) (erased (Nat) n)
       (erased (Edits a b n) reachable) (erased (AtLeast a b n) optimal) -> (Distance a b n))))

(def-adts
  ((Ranked : ((String) q) ((List (String)) ws) ((Nat) d) ((List (String)) rs) -> Type)
    enum
    (many RankedNil : (erased (String) q) (erased (Nat) d) -> (Ranked q (Nil (String)) d (Nil (String))))
    (many RankedTie : (erased (String) q) (erased (String) w) (erased (List (String)) ws) (erased (Nat) d) (erased (List (String)) rs)
       (erased (Distance q w d) dist) (erased (Ranked q ws d rs) rest)
       -> (Ranked q (Cons (String) w ws) d (Cons (String) w rs)))
    (many RankedFar : (erased (String) q) (erased (String) w) (erased (List (String)) ws) (erased (Nat) d) (erased (List (String)) rs)
       (erased (Nat) e) (erased (Distance q w e) dist) (erased (Lt d e) farther) (erased (Ranked q ws d rs) rest)
       -> (Ranked q (Cons (String) w ws) d rs))))

(def-adts
  ((Nearest : ((String) q) ((List (String)) ws) ((Nat) d) ((List (String)) rs) -> Type)
    enum
    (many NoWords : (erased (String) q) (erased (Nat) d) -> (Nearest q (Nil (String)) d (Nil (String))))
    (many Closest : (erased (String) q) (erased (List (String)) ws) (erased (Nat) d) (erased (String) r) (erased (List (String)) rs)
       (erased (Ranked q ws d (Cons (String) r rs)) ranked) -> (Nearest q ws d (Cons (String) r rs)))))
