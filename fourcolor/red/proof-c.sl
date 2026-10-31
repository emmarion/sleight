; all-red-proof: every configuration of configs.sl is C-reducible with its contract (cfreducible.v), by the certified check
; of ccheck.sl, one native.sl job per chunk of the css of chunks.sl, run by native-run. Load after chunks.sl and native.sl.

(native-each all-red-proof css (ch t r) (Chk (AllRed CRX ch)) (red-all-c ch (Nil _)) (CkY _ p) (ARCCons CRX ch t p r) (ARCNil CRX))
