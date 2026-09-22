; needs: cell_rev_inplace
; expect: (UCons _ 2 $ UCons _ 1 $ UCons _ 0 $ UNil _)
; The same in-place reversal carrying its correctness relation. RevOnto xs acc r reads
; reverse(xs) ++ acc = r, and its indices name xs and acc -- the cells the reversal overwrites. An erased
; mention may follow a binder's consumption (UNIQUE.md U2), so each branch builds its proof out of binders
; whose blocks have already been rewritten. Every entry of the proof is declared erased (section 20).

(def-adts
  ((RevOnto : (Type A) ((ULst A) xs) ((ULst A) acc) ((ULst A) r) -> Type)
    enum
    (many RONil : (erased Type A) (erased (ULst A) acc) -> (RevOnto A (UNil A) acc acc))
    (many ROCons : (erased Type A) (erased A hd) (erased (ULst A) tl) (erased (ULst A) acc)
                   (erased (ULst A) r) (erased (RevOnto A tl (UCons A hd acc) r) p)
                   -> (RevOnto A (UCons A hd tl) acc r))))

(def-fns _ $ (many rev-onto-proved : (erased Type A) (subterm unique (ULst A) xs) (unique (ULst A) acc) ->
    (unique (ULst A) r) (erased (RevOnto A xs acc r) p))
  (match unique xs _
    ((UNil _ c) (values acc (RONil _ acc)))
    ((UCons _ hd tl cell)
      (let ((unique r) (erased p)) (tail (rev-onto-proved _ tl (cell _ (at) hd acc))))
      (values r (ROCons _ hd tl acc r p)))))

(def-fns _ $ (many urev-proved : (erased Type A) (unique (ULst A) xs) ->
    (unique (ULst A) r) (erased (RevOnto A xs (UNil A) r) p))
  (rev-onto-proved _ xs (UNil _)))

(def-fns _ $ (many run-proved : -> (many (ULst (Nat)) r))
  (let ((unique xs)) (UCons _ 0 (UCons _ 1 (UCons _ 2 (UNil _)))))
  (let ((unique r) (erased proof)) (urev-proved _ xs))
  (share r))
run-proved
