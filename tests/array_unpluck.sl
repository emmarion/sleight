; expect: 7
; Section 44: an element is taken out of an array with `array-pluck`, whose `SetNth` proof
; names the element's own slot, mutated in place through its cell, and put back by `array-unpluck`, an
; at-function whose call is skipped: the array already holds the word.
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-fns _ $ (erased set-nth : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A y)
    (erased (List A) ys) (subterm erased (SetNth A xs i y ys) p) -> (erased (Nth A ys i y) q))
  (match erased p _
    ((SetHere _ _ _ _) (NthHere _ _ _))
    ((SetThere _ _ _ _ _ _ p1) (NthThere _ _ _ _ _ (set-nth _ _ _ _ _ p1)))))
(def-fns _ $ (many bump : (unique (Box) b) -> (unique (Box) r at b))
  (let-match unique b (MkBox n u))
  (u (Succ n)))
(def-fns _ $ (many go : -> (many (Nat) result))
  (let ((unique a)) (ACons _ _ (Init _ (MkBox 1)) (ACons _ _ (Init _ (MkBox 6)) (ANil (MaybeUninit (Box))))))
  (let ((unique item) (erased _) (unique b) (erased cleared)) (array-pluck _ _ a (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (let-match unique item (Init _ box))
  (let ((unique box2)) (bump box))
  (let ((erased _) (unique c) (erased restored)) (at erased (array-unpluck _ _ b (Succ (Zero)) box2 (set-nth _ _ _ _ _ cleared))))
  (let ((unique item2) (erased _) (unique _) (erased _)) (array-pluck _ _ c (Succ (Zero)) _ (set-nth _ _ _ _ _ restored)))
  (let-match unique item2 (Init _ box3))
  (let-match unique box3 (MkBox m))
  m)
(go)
; warns: tests/array_unpluck.sl:15:22: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1170:1: note: `;! warn` for `ACons` is here
; warns: tests/array_unpluck.sl:15:52: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1170:1: note: `;! warn` for `ACons` is here
