; embed4.sl's AllGc for the configurations of red/configs.sl (cfs as fcgoal.sl computes it), decided by one compiled run.
; Load after embed4.sl.

(let ((many cfs) (erased cl)) (concat-c (config-chunks)))

(goal erased (AllGc cfs))

(def-fns _ $ (many embed4-run : -> (many (Checked (AllGc cfs)) r)) (allgc-c cfs))

(let ((many res)) (native-compute embed4-run))
(comptime-match many res (ChkYes _ a))
(qed a)
