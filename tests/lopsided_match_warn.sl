; expect: 1

(def-adts $ (T : -> Type) enum (many Live : (many (Nat) n) -> (T)) (erased Ghost : (erased (Nat) n) -> (T)))
(def-adts $ (Wrap : -> Type) enum (many MkWrap : (many (Nat) n) -> (Wrap)))
(def-adts $ (Opt : -> Type) enum (many Full : (many (Nat) v) -> (Opt)) (many Empty : -> (Opt)))

(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Fn L (many (Nat) x) -> (many (Nat) y)) f) -> (Box)))
(def-lvl M)
(let ((erased lm)) (prove-predates L M))

(def-fns M
  ((many statements : (many (Nat) n) -> (many (Nat) r))
    (match many n _
      ((Zero) (Zero))
      ((Succ k) (let ((many j)) k) j)))
  ((many final-match : (many (Nat) n) -> (many (Nat) r))
    (match many n _
      ((Zero) (Zero))
      ((Succ k) (match many k _ ((Zero) k) ((Succ j) j)))))
  ((many single : (many (Wrap) w) -> (many (Nat) r))
    (match many w _
      ((MkWrap n) (match many n _ ((Zero) n) ((Succ k) k)))))
  ((erased erased-match : (erased (Nat) n) -> (erased (Nat) r))
    (match erased n _
      ((Zero) (Zero))
      ((Succ k) (let ((erased j)) k) j)))
  ((many in-branch : (many (Nat) n) -> (many (Nat) r))
    (match many n _
      ((Zero) (Zero))
      ((Succ k)
        (let ((many j)) k)
        (match many j _
          ((Zero) j)
          ((Succ i) (let ((many h)) i) h)))))
  ((many in-cell-match : (many (Nat) n) -> (many (Nat) r))
    (let ((many a)) (Zero))
    (let ((unique u)) (cell-alloc (Full (SlotHolds a))))
    (let ((unique v))
      (cell-match unique u (((Cell Full (SlotHolds a)) v at u))
        (Full s back)
        (match many n _
          ((Zero) back)
          ((Succ k) (let ((many j)) k) back))))
    (let ((many p)) (at (v a)))
    (let-match many p (Full x))
    x)
  ((many absurd-shallow : (many (Nat) n) (erased (Lt (Succ n) (Succ (Zero))) p) -> (many (Nat) r))
    (let-match erased p (LtS a b q))
    (match many n _
      ((Zero) (let ((many j)) n) j)
      (absurd (Succ k) q)))
  ((many two-deep : (many (Nat) n) -> (many (Nat) r))
    (match many n _
      ((Zero) (let ((many j)) n) j)
      ((Succ k) (let ((many j)) k) j)))
  ((many deep-else : (many (Nat) n) -> (many (Nat) r))
    (match many n _
      ((Zero) (Zero))
      (else (let ((many j)) n) j)))
  ((many deep-absurd : (many (Nat) n) (erased (Lt n (Succ (Zero))) p) -> (many (Nat) r))
    (match many n _
      ((Zero) n)
      (absurd (Succ k) (let-match erased p (LtS a b q)) q)))
  ((many buried : (many (Nat) n) -> (many (Nat) r))
    (match many n _
      ((Zero) (Zero))
      ((Succ k) (Succ (match many k _ ((Zero) k) ((Succ j) j))))))
  ((many in-let : (many (Nat) n) -> (many (Nat) r))
    (let ((many m))
      (match many n (((Nat) x))
        ((Zero) (Zero))
        ((Succ k) (let ((many j)) k) j)))
    m)
  ((many phantom : (many (T) t) -> (many (Nat) r))
    (match many t _
      ((Live n) n)
      ((Ghost n) (let ((erased j)) n) j)))
  ((many shadowed : (many (Box) b) (many (Nat) n) -> (many (Nat) r))
    (match many b _
      ((MkBox match) (match n)))))

(let ((many top))
  (match many (Zero) (((Nat) x))
    ((Zero) (let ((many j)) (Zero)) j)
    (absurd Succ)))

(let ((many a)) (Zero))
(let ((unique u)) (cell-alloc (Full (SlotHolds a))))
(let ((unique v))
  (cell-match unique u (((Cell Full (SlotHolds a)) v at u))
    (Full s back)
    (match many top _
      ((Zero) (let ((many j)) top) back)
      ((Succ k) back))))

(match many (shadowed (MkBox inc) (statements (in-cell-match (Succ (Succ (Succ top)))))) (((Nat) x))
  ((Zero) (Zero))
  ((Succ k) (let ((many j)) k) (Succ j)))
; warns: tests/lopsided_match_warn.sl:15:6: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/lopsided_match_warn.sl:19:6: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/lopsided_match_warn.sl:23:6: warning: lopsided `match`; flatten it with a `let-match` on `MkWrap`
; warns: tests/lopsided_match_warn.sl:26:6: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/lopsided_match_warn.sl:34:10: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/lopsided_match_warn.sl:30:6: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/lopsided_match_warn.sl:43:10: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/lopsided_match_warn.sl:51:6: warning: lopsided `match`; flatten it with a `let-match` on `Zero`
; warns: tests/lopsided_match_warn.sl:82:15: warning: declaration of `match` shadows a built-in
; warns: tests/lopsided_match_warn.sl:94:6: warning: lopsided `match`; flatten it with a `let-match` on `Zero`
