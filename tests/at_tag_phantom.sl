; expect: (MkTok _)
(def-adts $ (Tok : -> Type) enum
  (many MkTok : (erased (Nat) n) -> (Tok)))

(def-adts $ (Ph : -> Type) union
  (many PA : -> (Ph))
  (erased PG : (erased (Nat) n) -> (Ph)))

(def-fns _ $ (erased vacant : (erased (Ph) _p at vacant-slot) ->)
  (values))

(def-fns _ $ (erased tagged : (erased (Ph) p) ->)
  (match erased p ()
    ((PA) (slot-tag p) (vacant p))
    ((PG _) (slot-tag p) (vacant p))))

(def-fns _ $ (many at ph-tok : (many (Ph) p) -> (many (Tok) t at p))
  (slot-tag p)
  (MkTok 0))

(ph-tok (PA))
