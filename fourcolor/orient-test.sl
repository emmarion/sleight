; slc std/macro.sl std/nat.sl std/list.sl fourcolor/ring.sl fourcolor/defs.sl fourcolor/orient.sl fourcolor/orient-test.sl --goal proved
(comptime-match many (left-dec (MkPoint 0 0) (MkPoint 2 0) (MkPoint 1 1)) (OLeft _ _ _ _))
(comptime-match many (left-dec (MkPoint 2 0) (MkPoint 0 0) (MkPoint 1 1)) (ORight _ _ _ _))
(comptime-match many (left-dec (MkPoint 0 0) (MkPoint 1 1) (MkPoint 3 3)) (OOn _ _ _ _))

(def-adts $ (CC : -> Type)
  enum
  (many MkCC : (erased (Level) L1 L2 L3 L4 L5)
      (erased (Fn L1 (erased (Point) p q r) (erased (Left p q r) l) -> (erased (Left q r p) m)) cyclic)
      (erased (Fn L2 (erased (Point) p q r) (erased (Left p q r) l) (erased (Left q p r) m) -> (erased (False) f)) antisym)
      (erased (Fn L3 (many (Point) p q r) -> (many (Orient p q r) o)) trichotomy)
      (erased (Fn L4 (erased (Point) p q r t) (erased (Left t q r) l1) (erased (Left p t r) l2) (erased (Left p q t) l3) ->
          (erased (Left p q r) l)) interior)
      (erased (Fn L5 (erased (Point) t s p q r) (erased (Left t s p) l1) (erased (Left t s q) l2) (erased (Left t s r) l3)
          (erased (Left t p q) l4) (erased (Left t q r) l5) -> (erased (Left t p r) l)) transitive)
      -> (CC)))

(goal erased (CC))
(qed (MkCC (level-of left-rot) (level-of left-antisym) (level-of left-dec) (level-of left-interior) (level-of left-trans)
  left-rot left-antisym left-dec left-interior left-trans))
