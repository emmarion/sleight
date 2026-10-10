; error: `M2` was not in scope when level `L` was minted
(def-lvl L)
(def-lvl M)
(let ((erased M2)) M)
(let ((erased p)) (prove-predates M2 L))
