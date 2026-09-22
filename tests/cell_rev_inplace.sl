; expect: (UCons _ 2 $ UCons _ 1 $ UCons _ 0 $ UNil _)
; Pointer reversal in place. The spine's fields are unique, so a unique destructure hands back the cons
; cell each node occupied (UNIQUE.md U5), and reinvoking that cell with the accumulator reuses the block.
; The head slot already holds hd, so (at) skips its store: one store per node, no allocation, and the
; recursive call is a tail call.

(def-adts $ (ULst : (Type A) -> Type)
  enum
  (many UNil : (erased Type A) -> (ULst A))
  (many UCons : (erased Type A) (many A head) (unique (ULst A) tail) -> (ULst A)))

(def-fns _ $ (many rev-onto : (erased Type A) (subterm unique (ULst A) xs) (unique (ULst A) acc) ->
    (unique (ULst A) r))
  (match unique xs _
    ((UNil _ c) acc)
    ((UCons _ hd tl cell) (tail (rev-onto _ tl (cell _ (at) hd acc))))))

(def-fns _ $ (many urev : (erased Type A) (unique (ULst A) xs) -> (unique (ULst A) r))
  (rev-onto _ xs (UNil _)))

(def-fns _ $ (many run : -> (many (ULst (Nat)) r))
  (let ((unique xs)) (UCons _ 0 (UCons _ 1 (UCons _ 2 (UNil _)))))
  (share (urev _ xs)))
run
