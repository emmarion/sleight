(def-adts $ (StronglyNormalizing : -> Type)
  enum
  (many MkSN : (erased (TyCtor ((Term) t) -> Type) P) (erased (Level) L)
     (erased (Fn L (erased (List (Ty)) g) (erased (Term) t) (erased (Ty) a) (erased (Typed g t a) h) -> (erased (P t) d)) typed)
     (erased (Fn L (erased (Term) t u) (erased (P t) d) (erased (Step t u) s) -> (erased (P u) e) (erased (Subterm (P u) e (P t) d) dec)) step)
     -> (StronglyNormalizing)))

(goal erased (StronglyNormalizing))
