; expect: 3
; A resource whose type index records its protocol state, threaded linearly. Uniqueness makes each
; operation consume its handle, so a spent one cannot be used again, and the index is what fixes the
; order: do-send and do-close take an (Opened) handle and only do-open produces one. The state lives in
; an erased index and each transition reinvokes the handle's own cell, so do-open's body is a full-at
; invocation of a cell it already fills and its result is an at return.

(def-adts $ (St : -> Type)
  enum
  (many Closed : -> (St))
  (many Opened : -> (St)))

(def-adts $ (Conn : ((St) s) -> Type)
  enum
  (many MkConn : (erased (St) s) (many (Nat) fd) -> (Conn s)))

(def-fns _ $ (many do-open : (unique (Conn (Closed)) c) -> (unique (Conn (Opened)) r at c))
  (match unique c _
    ((MkConn _ fd cell) (at (cell _ fd)))))

(def-fns _ $ (many do-send : (unique (Conn (Opened)) c) (many (Nat) msg) -> (unique (Conn (Opened)) r at c))
  (match unique c _
    ((MkConn _ fd cell) (cell _ (nat-add fd msg)))))

(def-fns _ $ (many do-close : (unique (Conn (Opened)) c) -> (many (Nat) total))
  (match unique c _
    ((MkConn _ fd cell) fd)))

(def-fns _ $ (many session : -> (many (Nat) n))
  (let ((unique (Conn (Closed)) c)) (MkConn (Closed) 0))
  (let ((unique c1)) (do-open c))
  (let ((unique c2)) (do-send c1 1))
  (let ((unique c3)) (do-send c2 2))
  (do-close c3))
session
