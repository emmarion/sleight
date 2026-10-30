; notembed.sl's CfCerts for the configurations of red/configs.sl (cfs as fcgoal.sl computes it), from embed4.sl's AllGc,
; decided by one compiled run. Load after embed4.sl.

(let ((many cfs) (erased cl)) (concat-c (config-chunks)))

(goal erased (CfCerts cfs))

(def-fns _ $ (many embed4-run : -> (many (Checked (AllGc cfs)) r)) (allgc-c cfs))

(let ((many res)) (native-compute embed4-run))
(comptime-match many res (ChkYes _ a))
(qed (cfcerts-of cfs a))
