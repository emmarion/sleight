; Checks no-mce of embed.sl as a goal. Load after embed.sl.
(def-adts $ (NoMce : -> Type)
  enum
  (many MkNoMce : (erased (Level) F)
      (erased (Fn F (erased (List (List (Config))) css) (erased (List (Config)) cfs) (erased (ConcatL css cfs) cl) (erased (AllRedC css) ar)
          (erased (UnavE cfs) u) (erased (BirkGeo) bg) (erased (NotEmbed cfs) ne) -> (erased (Level) G)
          (erased (Fn G (erased (Level) L1 L2) -> (erased (Level) M)
              (erased (Fn M (erased (Nat) d) (erased (List (Nat)) e n f) (erased (MinimalCounterExample L1 L2 d e n f) mce) -> (erased (False) r)) r)) fac))
        nm)
      -> (NoMce)))

(goal erased (NoMce))
(qed (MkNoMce (level-of no-mce) no-mce))
