; all-red-proof: every configuration of configs.sl is C-reducible with its contract (cfreducible.v), by the certified check
; of ccheck.sl, one native.sl job per piece of pcs (pieces.sl), run by native-run. Load after pieces.sl and native.sl.

(native-each pieces-red-proof pcs (pc t r) (Chk (AllRed CRX pc)) (red-all-c pc (Nil _)) (CkY _ p) (ARCCons CRX pc t p r) (ARCNil CRX))
(native-then (let ((erased all-red-proof)) (allredc-pieces CRX pcs css cfs-all pcs-cat cfs-cat pieces-red-proof)))
