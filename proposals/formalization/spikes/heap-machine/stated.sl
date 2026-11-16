(def-lvl stated)

(let ((erased small-big))
  (Fn stated (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) c) (erased (List (Label)) ls)
    (erased (Heap) h2) (erased (Word) w)
    (erased (Steps fns h (KRun env c (KNil)) ls h2 (KRet w (KNil))) d) ->
    (erased (Choices) ch) (erased (Run fns h env c ch h2 w) r)))
