; work/sort.sl: certified in-place sort (milestone 3: heapsort).
; The function `heapsort-fast` is what accept.sl calls: it heapifies the array
; with the build loop (work/loops.sl's `build-loop`, sifting nodes q-1 .. 0 for
; q = n >> 1) and then extracts with `ext-loop`, returning a certified sorted
; permutation. The array writes go through `swap2-imm` (work/u62imm.sl), which
; coerces the Copy (Nat) array to Copy (U62), does the two writes as -imm
; forms, and coerces back -- so no `array-swap`/`array-place` and no
; suppressions.

(def-fns _ $ (many heapsort-fast : (erased (List (Nat)) xs) (erased (AllTo (Nat) Lt xs u62-modulus) small)
    (erased (Nat) n) (erased (Length (Nat) xs n) len) (erased (Lt n max-array-length) fits0)
    (erased (List (Copy (Nat))) cs) (unique (Array (Copy (Nat)) cs) a) (erased (Copies (Nat) xs cs) rel) ->
    (erased (List (Nat)) ys) (erased (List (Copy (Nat))) ds) (unique (Array (Copy (Nat)) ds) r at a)
    (erased (Copies (Nat) ys ds) rel2) (erased (SortedPerm (Nat) Le xs ys) correct))
  (let ((erased fits)) (lt-trans n max-array-length u62-modulus fits0 max-array-length-below-u62))
  (let ((many n2) (erased clen) (unique a0)) (array-length (Copy (Nat)) cs a))
  (let-match erased (copies-length-fn xs cs n n2 len clen rel) (Refl _ _))
  (let ((many q) (erased v1) (erased pv1) (erased m1) (erased r1) (erased mm1) (erased ad1) (erased rlt1) (erased pq1))
    (u62-shr n2 1 fits (shift-one-lt)))
  (let ((erased hfd)) (hf-of n2 v1 pv1 q m1 mm1 r1 ad1 rlt1 pq1))
  (let-match many (u62-lt-dec (Zero) q u62-modulus-pos pq1) (Yes _ _ _ _ qpos)
    ((No _ _ _ _ le-qz) (let ((erased qz)) (lt-eq-succ _ _ le-qz))
      (let-match erased qz (LtZ _) (absurd (LtS _ _ z1) z1))
      (let-match erased hfd (MkHf _ _ _ mm _ ad rl _))
      (let-match erased mm (MulZero _))
      (let-match erased ad (AddZero _))
      (let ((erased heap0)) (HLeaf xs n (Zero) (Zero) (D0) rl))
      (let ((erased ys2) (erased ds2) (unique r) (erased rel2) (erased perm2) (erased asc2))
        (ext-loop n2 xs n fits xs cs a0 rel len small (perm-refl xs)
          xs (Nil (Nat)) (split-full xs n len) (AscNil (Nat) Le) (rangele-nil xs) heap0 (lt-succ n)))
      (values ys2 ds2 r rel2 (MkSortedPerm (Nat) Le xs ys2 asc2 perm2))))
  (let-match erased qpos (LtZ qz))
  (let ((many j0)) (u62-dec qz q pq1))
  (let ((erased dj0) (erased ddj0)) (double qz))
  (let ((erased binv0)) (binv-leaves xs n q hfd qz dj0 ddj0 (le-refl q)))
  (let ((erased ys2) (erased ds2) (unique r) (erased rel2) (erased perm2) (erased ly2) (erased bnd2) (erased heap0))
    (build-loop j0 dj0 ddj0 xs n2 fits xs cs a0 rel len small (perm-refl xs) binv0 q hfd (lt-succ qz)))
  (let ((erased ys3) (erased ds3) (unique r2) (erased rel3) (erased perm3) (erased asc3))
    (ext-loop n2 xs n fits ys2 ds2 r rel2 ly2 bnd2 perm2
      ys2 (Nil (Nat)) (split-full ys2 n ly2) (AscNil (Nat) Le) (rangele-nil ys2) heap0 (lt-succ n)))
  (values ys3 ds3 r2 rel3 (MkSortedPerm (Nat) Le xs ys3 asc3 perm3)))
