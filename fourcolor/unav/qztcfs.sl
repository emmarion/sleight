; cfs, the configurations of red/configs.sl decoded from config-srcs (cfs-dec its DecList), which qztproof.sl reads, and
; cfs-run, which decodes it again in a native job as fcopen.sl's does. Load after present.sl.

(comptime-match many (dec-list config-srcs) (POk _ _ _ _ cfs _ cfs-dec))

(def-fns _ $ (many cfs-run : -> (many (List (Config)) c) (many (Checked (Eq (List (Config)) c cfs)) e))
  (let-match many (dec-list config-srcs) (POk _ _ _ _ c _ d) (else (values (Nil _) (ChkNo _))))
  (values c (ChkYes _ (declist-fn config-srcs _ _ c cfs d cfs-dec))))
