; Checks embed-analysis of embed.sl as a goal. Load after embed.sl.
(def-adts $ (EmbedAnalysis : -> Type)
  enum
  (many MkEmbedAnalysis : (erased (Level) F)
      (erased (Fn F (erased (Level) X) (erased (List (List (Config))) css) (erased (List (Config)) cfs) (erased (ConcatL css cfs) cl) (erased (AllRedC X css) ar)
          (erased (UnavE cfs) u) (erased (BirkGeo) bg) (erased (NotEmbed X cfs) ne) -> (erased (Analysis) an))
        ea)
      -> (EmbedAnalysis)))

(goal erased (EmbedAnalysis))
(qed (MkEmbedAnalysis (level-of embed-analysis) embed-analysis))
