; expect: 7
; AT_REDESIGN A12's follow-up 11: an element is taken out of an array with `array-pluck`, whose `ASet` proof
; names the element's own slot, mutated in place through its cell, and put back by `array-unpluck`, an
; at-function whose call is skipped: the array already holds the word.
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-fns _ $ (erased aset-anth : (erased Type A) (erased (Nat) n) (erased (Array A n) a) (erased (Nat) i) (erased A y)
    (erased (Array A n) r) (subterm erased (ASet A n a i y r) p) -> (erased (ANth A n r i y) q))
  (match erased p _
    ((SetZ _ _ _ _ _) (NthZ _ _ _ _))
    ((SetS _ _ _ _ _ _ _ p1) (NthS _ _ _ _ _ _ (aset-anth _ _ _ _ _ _ p1)))))
(def-fns _ $ (many bump : (unique (Box) b) -> (unique (Box) r at b))
  (let-match unique b (MkBox n u))
  (u (Succ n)))
(def-fns _ $ (many go : -> (many (Nat) result))
  (let ((unique a)) (ACons _ _ (Init _ (MkBox 1)) (ACons _ _ (Init _ (MkBox 6)) (ANil (MaybeUninit (Box))))))
  (let ((unique item) (unique b) (erased cleared)) (array-pluck _ _ a (Succ (Zero)) _ (NthS _ _ _ _ _ _ (NthZ _ _ _ _))))
  (let-match unique item (Init _ box))
  (let ((unique box2)) (bump box))
  (let ((unique c) (erased restored)) (array-unpluck _ _ b (Succ (Zero)) box2 (aset-anth _ _ _ _ _ _ cleared)))
  (let ((unique item2) (unique d) (erased cleared2)) (array-pluck _ _ c (Succ (Zero)) _ (aset-anth _ _ _ _ _ _ restored)))
  (let-match unique item2 (Init _ box3))
  (let-match unique box3 (MkBox m))
  m)
(go)
; warns: tests/array_unpluck.sl:15:22: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:976:1: note: `;! warn` for `ACons` is here
; warns: tests/array_unpluck.sl:15:52: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:976:1: note: `;! warn` for `ACons` is here
