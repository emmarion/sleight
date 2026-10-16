; externs: only
(def-adts $ (Tree : -> Type) enum
  (many Leaf : -> (Tree))
  (many Node : (many (Tree) l) (many (Tree) r) -> (Tree)))

(def-fns _ $ (many visit : (erased (List (Slot)) xs) (subterm many (Tree) t) (unique (Slots xs) seen) ->
    (erased (List (Slot)) ys) (unique (Slots ys) seen2 at seen))
  (let ((erased xs1) (many r) (unique s1)) (slots-intern _ seen (slot-of t)))
  (let-match many r (SlotAdded _ _ _ _) ((SlotExisting _ _ _ _) (values xs1 s1)))
  (let-match many t (Node l rt) ((Leaf) (values xs1 s1)))
  (let ((erased xs2) (unique s2)) (notail $ visit _ l s1))
  (tail $ visit _ rt s2))

(def-fns _ $ (many distinct : (many (Tree) t) -> (many (Nat) n))
  (let ((unique s0)) (slots-new))
  (let ((erased xs) (unique s1)) (visit _ t s0))
  (let ((many n) (erased _) (unique _)) (slots-length _ s1))
  n)

(def-fns _ $ (many tower : (subterm many (Nat) k) -> (many (Tree) t))
  (let-match many k (Succ j) ((Zero) (Leaf)))
  (let ((many s)) (notail $ tower j))
  (Node s s))

(def-fns _ $ (many comb : (many (Tree) b) (subterm many (Nat) k) -> (many (Tree) t))
  (let-match many k (Succ j) ((Zero) b))
  (let ((many s)) (notail $ comb b j))
  (Node s b))

(def-fns _ $ (many run : -> (many (List (Nat)) out))
  (let ((many leaf)) (Leaf))
  (Cons _ (distinct (tower 300)) $ Cons _ (distinct (comb (Node leaf leaf) 20000)) $ Nil _))

run
; expect: (Cons _ 301 $ Cons _ 20002 $ Nil _)
