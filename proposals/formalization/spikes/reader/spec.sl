(def-adts $ (Reader : -> Type)
  enum
  (many MkReader : (erased (Level) L N D M)
     (many (Fn L (many (String) text) -> (many (Read text) r)) read)
     (erased (Fn N (erased (String) text) (erased (List (Form)) forms) (erased (Mistake) m)
                   (erased (Reads text forms) p) (erased (Unreadable text m) q) -> (erased (False) f)) never-both)
     (erased (Fn D (erased (String) text) (erased (List (Form)) f1 f2)
                   (erased (Reads text f1) p) (erased (Reads text f2) q) -> (erased (Eq (List (Form)) f1 f2) e)) one-reading)
     (erased (Fn M (erased (String) text) (erased (Mistake) m1 m2)
                   (erased (Unreadable text m1) p) (erased (Unreadable text m2) q) -> (erased (Eq (Mistake) m1 m2) e)) one-mistake)
     -> (Reader)))

(goal many (Reader))
