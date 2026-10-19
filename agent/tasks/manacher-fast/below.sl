(def-adts
  ((AllBelow : ((List (Nat)) xs) ((Nat) m) -> Type)
    enum
    (many BelowNil : (erased (Nat) m) -> (AllBelow (Nil (Nat)) m))
    (many BelowCons : (erased (Nat) x) (erased (List (Nat)) xs) (erased (Nat) m)
        (erased (Lt x m) p) (erased (AllBelow xs m) rest) -> (AllBelow (Cons (Nat) x xs) m))))

(def-adts
  ((Copies : ((List (Nat)) xs) ((List (Copy (Nat))) cs) -> Type)
    enum
    (many CopiesNil : -> (Copies (Nil (Nat)) (Nil (Copy (Nat)))))
    (many CopiesCons : (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Copy (Nat))) cs)
        (erased (Copies xs cs) rest) -> (Copies (Cons (Nat) x xs) (Cons (Copy (Nat)) (MkCopy (Nat) x) cs)))))

(def-adts
  ((Manacher : -> Type)
    enum
    (many ManacherList : (erased (Level) L)
        (many (Fn L (many (List (Nat)) xs) -> (many (Nat) n) (erased (LongestPalindrome xs n) correct)) f) -> (Manacher))
    (many ManacherArray : (erased (Level) L)
        (many (Fn L (erased (List (Nat)) xs) (erased (AllBelow xs u62-modulus) small)
            (erased (Nat) len) (erased (Length (Nat) xs len) lp) (erased (Lt len u62-modulus) fits)
            (erased (List (Copy (Nat))) cs) (unique (Array (Copy (Nat)) cs) a) (erased (Copies xs cs) rel) ->
            (many (Nat) n) (erased (LongestPalindrome xs n) correct)) f) -> (Manacher))))
(goal many (Manacher))
