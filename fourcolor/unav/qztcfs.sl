; cfs, the configurations of red/configs.sl, which qztproof.sl reads, and cfs-run, which gives it to a native job as fcopen.sl's
; does. Load after present.sl.

(let ((many cfs)) (concat-cfs (config-chunks)))

(def-fns _ $ (many cfs-run : -> (many (List (Config)) c) (many (Checked (Eq (List (Config)) c cfs)) e)) (values cfs (ChkYes _ (Refl _ cfs))))
