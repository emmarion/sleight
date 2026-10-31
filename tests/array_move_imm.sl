; expect: (MkPair _ _ (MkU62 99 _) $ MkU62 100 _)
(def-fns _ $ (many char-u62 : (many (Char) c) -> (many (U62) u))
  (let-match erased c (MkChar b))
  (let-match erased b (MkU8 n p))
  (let ((erased q)) (lt-trans n u8-modulus u62-modulus p u8-below-u62))
  (coerce c (coercible-trans
              (coercible-trans (coercible-sym (coercible-wrap (Shared) MkChar b)) (coercible-sym (coercible-wrap (Shared) MkU8 n p)))
              (coercible-wrap (Shared) MkU62 n q))))

(def-fns _ $ (many fresh-u62 : (many (Char) c) -> (unique (U62) u))
  (let-match many (char-u62 c) (MkU62 n q))
  (MkU62 n q))

(def-fns _ $ (many move-test : -> (many (Pair (U62) (U62)) result))
  (let ((unique a)) (fresh-u62 #\c))
  (let ((unique b)) (fresh-u62 #\d))
  (let ((unique src))
    (ACons _ _ (Init _ (MkUSlotItem _ _ _ (place-at _ a)))
      (ACons _ _ (Init _ (MkUSlotItem _ _ _ (place-at _ b))) (ANil (MaybeUninit (USlotItem (U62)))))))
  (let ((unique dst))
    (ACons _ _ (Vacant _ vacant-slot) (ACons _ _ (Vacant _ vacant-slot)
      (ACons _ _ (Vacant _ vacant-slot) (ANil (MaybeUninit (USlotItem (U62))))))))
  (let ((erased _) (erased _) (erased _) (unique r) (unique s) (erased p) (erased q) (erased v))
    (array-move-imm _ _ _ _ _ src (Zero) dst (Succ (Zero)) (Succ (Succ (Zero)))
      (SpliceHere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceNil _ _)
      (SpliceThere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceHere _ _ _ _ _ _ _ $ SpliceNil _ _)
      (ImmU62)))
  (let-match erased p (SpliceThere _ _ _ _ _ _ _ p1))
  (let-match erased p1 (SpliceHere _ _ _ _ _ _ _ p2))
  (let-match erased p2 (SpliceHere _ _ _ _ _ _ _ p3))
  (let-match erased p3 (SpliceNil _ _))
  (let-match erased q (SpliceHere _ _ _ _ _ _ _ q1))
  (let-match erased q1 (SpliceHere _ _ _ _ _ _ _ q2))
  (let-match erased q2 (SpliceNil _ _))
  (let-match erased v (VacatedInit _ _ _ _ _ _ _ v1))
  (let-match erased v1 (VacatedInit _ _ _ _ _ _ _ _))
  (let-match unique s (ACons _ _ u0 s1))
  (let-match unique s1 (ACons _ _ u1 _))
  (let-match unique u0 (Stale _ sa _ _))
  (let-match unique u1 (Stale _ sb _ _))
  (let ((erased (Eq (Slot) sa (slot-of a)) _)) (Refl _ _))
  (let ((erased (Eq (Slot) sb (slot-of b)) _)) (Refl _ _))
  (let-match unique r (ACons _ _ _ r1))
  (let-match unique r1 (ACons _ _ e1 r2))
  (let-match unique r2 (ACons _ _ e2 _))
  (let-match unique e1 (Init _ i1))
  (let-match unique e2 (Init _ i2))
  (let-match unique i1 (MkUSlotItem _ _ _ pa))
  (let-match unique i2 (MkUSlotItem _ _ _ pb))
  (MkPair _ _ (share (unplace-at _ _ _ pa)) (share (unplace-at _ _ _ pb))))
move-test
; warns: tests/array_move_imm.sl:18:6: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1289:1: note: `;! warn` for `ACons` is here
; warns: tests/array_move_imm.sl:19:8: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1289:1: note: `;! warn` for `ACons` is here
; warns: tests/array_move_imm.sl:21:6: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1289:1: note: `;! warn` for `ACons` is here
; warns: tests/array_move_imm.sl:21:40: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1289:1: note: `;! warn` for `ACons` is here
; warns: tests/array_move_imm.sl:22:8: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1289:1: note: `;! warn` for `ACons` is here
; warns: tests/array_move_imm.sl:37:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1290:1: note: `;! warn` for `Array` is here
; warns: tests/array_move_imm.sl:38:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1290:1: note: `;! warn` for `Array` is here
; warns: tests/array_move_imm.sl:43:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1290:1: note: `;! warn` for `Array` is here
; warns: tests/array_move_imm.sl:44:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1290:1: note: `;! warn` for `Array` is here
; warns: tests/array_move_imm.sl:45:3: warning: match on `Array`: copies the array's tail, O(n); read with `array-get` and `array-length`, or their `-many` forms at many
; warns: lib/prelude.sl:1290:1: note: `;! warn` for `Array` is here
