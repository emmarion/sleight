(def-lvl W)
(def-lvl K)

(def-adts $ (XM : -> Type)
  enum
  (many XRet : (many (Nat) v) -> (XM))
  (many XAsk : (many (Nat) s) (many (Fn K (many (XTree) out) -> (many (XM) next)) k) -> (XM))
  (many XBind : (many (XM) m) (many (Fn K (many (Nat) v) -> (many (XM) next)) f) -> (XM)))

(def-fns W $ (many xwalk : (subterm many (XTree) t) -> (many (XM) m))
  (match many t _
    ((XGen) (XRet 1))
    ((XNode l r)
      (def-fns K $ (many after-l : (many (Nat) a) -> (many (XM) next))
        (def-fns K $ (many after-r : (many (Nat) b) -> (many (XM) next))
          (XRet (nat-add a b)))
        (XBind (xwalk r) after-r))
      (XBind (notail $ xwalk l) after-l))
    ((XExpand s)
      (def-fns K $ (many expanded : (many (XTree) out) -> (many (XM) next))
        (xwalk out))
      (XAsk s expanded))))

(MkUnit)
