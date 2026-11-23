(def-adts $ (Tk : -> Type)
  enum
  (many Tp : -> (Tk))
  (many T0 : -> (Tk))
  (many T1 : -> (Tk)))

(def-adts $ (Tl : -> Type)
  enum
  (many TlE : -> (Tl))
  (many Tl1 : -> (Tl))
  (many Tl11 : -> (Tl))
  (many Tl011 : -> (Tl))
  (many Tl0011 : -> (Tl)))

(def-adts
  ((TpR : ((Nat) m) ((List (Tk)) R) ((List (Tk)) R2) -> Type)
    enum
    (many TpZ : (erased (List (Tk)) R) -> (TpR (Zero) R R))
    (many TpS : (erased (Nat) m) (erased (List (Tk)) R R2) (erased (TpR m R R2) p) -> (TpR (Succ m) R (Cons (Tk) (Tp) R2)))))

(def-adts
  ((Tl0 : ((List (Tk)) R) ((List (Tk)) R2) -> Type)
    enum
    (many Tl0N : -> (Tl0 (Nil (Tk)) (Nil (Tk))))
    (many Tl0P : (erased (List (Tk)) R) -> (Tl0 (Cons (Tk) (Tp) R) R))
    (many Tl01 : (erased (List (Tk)) R) -> (Tl0 (Cons (Tk) (T1) R) (Cons (Tk) (T0) R)))))

(def-adts $ (SRes : -> Type)
  enum
  (many STurn : (many (List (Nat)) K) (many (List (Tk)) W) -> (SRes))
  (many SEnd : (many (List (Nat)) K) -> (SRes)))

(def-adts
  ((Sw : ((List (Nat)) K) ((List (Tk)) R) ((SRes) s) -> Type)
    enum
    (many SwEnd : (erased (List (Nat)) K) -> (Sw K (Nil (Tk)) (SEnd K)))
    (many SwT0 : (erased (List (Nat)) K) (erased (List (Tk)) R) (erased (SRes) s)
       (erased (Sw (Cons (Nat) (Succ (Succ (Zero))) K) R s) p) -> (Sw K (Cons (Tk) (T0) R) s))
    (many SwT1 : (erased (List (Nat)) K) (erased (List (Tk)) R) (erased (SRes) s)
       (erased (Sw (Cons (Nat) (Succ (Succ (Succ (Zero)))) K) R s) p) -> (Sw K (Cons (Tk) (T1) R) s))
    (many SwP0 : (erased (List (Nat)) K) (erased (List (Tk)) R) (erased (SRes) s)
       (erased (Sw (Cons (Nat) (Succ (Succ (Succ (Zero)))) K) R s) p) -> (Sw K (Cons (Tk) (Tp) (Cons (Tk) (T0) R)) s))
    (many SwP1T : (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) R W) (erased (TpR m (Cons (Tk) (T1) (Cons (Tk) (T0) R)) W) p)
       -> (Sw (Cons (Nat) (Succ (Succ (Succ m))) K) (Cons (Tk) (Tp) (Cons (Tk) (T1) R)) (STurn K W)))
    (many SwP1M : (erased (Nat) s) (erased (List (Nat)) K) (erased (List (Tk)) R) (erased (SRes) z)
       (erased (Sw (Cons (Nat) (Succ (Succ (Zero))) (Cons (Nat) (Succ (Succ (Succ (Zero)))) (Cons (Nat) (Succ s) K))) R z) p)
       -> (Sw (Cons (Nat) (Succ (Succ (Zero))) (Cons (Nat) s K)) (Cons (Tk) (Tp) (Cons (Tk) (T1) R)) z))
    (many SwPPT : (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) R W) (erased (TpR m (Cons (Tk) (T1) R) W) p)
       -> (Sw (Cons (Nat) (Succ (Succ (Succ m))) K) (Cons (Tk) (Tp) (Cons (Tk) (Tp) R)) (STurn K W)))
    (many SwPPM : (erased (Nat) s) (erased (List (Nat)) K) (erased (List (Tk)) R) (erased (SRes) z)
       (erased (Sw (Cons (Nat) (Succ (Succ (Succ (Zero)))) (Cons (Nat) (Succ s) K)) R z) p)
       -> (Sw (Cons (Nat) (Succ (Succ (Zero))) (Cons (Nat) s K)) (Cons (Tk) (Tp) (Cons (Tk) (Tp) R)) z))))

(def-adts
  ((Wk : ((List (Nat)) K) ((List (Tk)) R) ((List (Tk)) Y) -> Type)
    enum
    (many WkN : (erased (List (Tk)) R) -> (Wk (Nil (Nat)) R R))
    (many WkC : (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) R R1 R2 Y) (erased (Tl0 R R1) tl)
       (erased (TpR m (Cons (Tk) (T1) R1) R2) tp) (erased (Wk K R2 Y) w) -> (Wk (Cons (Nat) (Succ (Succ m)) K) R Y))))

(def-adts
  ((Plain : ((Tl) T) -> Type)
    enum
    (many PlE : -> (Plain (TlE)))
    (many Pl1 : -> (Plain (Tl1)))))

(def-adts
  ((En : ((List (Nat)) K) ((Tl) T) ((List (Nat)) K2) ((List (Tk)) W) ((Tl) T2) ((Nat) c) -> Type)
    enum
    (many En11 : (erased (List (Nat)) K)
       -> (En K (Tl11) K (Cons (Tk) (Tp) (Nil (Tk))) (Tl011) (Succ (Succ (Succ (Succ (Zero)))))))
    (many En011 : (erased (List (Nat)) K)
       -> (En K (Tl011) K (Cons (Tk) (Tp) (Nil (Tk))) (Tl0011) (Succ (Succ (Succ (Succ (Zero)))))))
    (many EnTP : (erased (Tl) T) (erased (Plain T) pl) (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) W)
       (erased (TpR m (Cons (Tk) (T1) (Nil (Tk))) W) p) -> (En (Cons (Nat) (Succ (Succ (Succ m))) K) T K W T (Succ (Succ (Zero)))))
    (many EnT4 : (erased (Nat) m) (erased (List (Nat)) K) (erased (List (Tk)) W)
       (erased (TpR m (Cons (Tk) (T1) (Nil (Tk))) W) p) -> (En (Cons (Nat) (Succ (Succ (Succ m))) K) (Tl0011) K W (Tl11) (Zero)))
    (many EnMP : (erased (Tl) T) (erased (Plain T) pl) (erased (Nat) s) (erased (List (Nat)) K)
       -> (En (Cons (Nat) (Succ (Succ (Zero))) (Cons (Nat) s K)) T (Cons (Nat) (Succ s) K) (Cons (Tk) (T1) (Nil (Tk))) T
             (Succ (Succ (Succ (Succ (Zero)))))))
    (many EnM4 : (erased (Nat) s) (erased (List (Nat)) K)
       -> (En (Cons (Nat) (Succ (Succ (Zero))) (Cons (Nat) s K)) (Tl0011)
             (Cons (Nat) (Succ (Succ (Succ (Zero)))) (Cons (Nat) (Succ s) K)) (Cons (Tk) (Tp) (Nil (Tk))) (Tl011)
             (Succ (Succ (Succ (Succ (Zero)))))))))

(def-adts
  ((Rd : ((List (Tk)) X) ((Tl) T) ((List (Tk)) Y) ((Tl) T2) ((Nat) c) -> Type)
    enum
    (many RdT : (erased (List (Tk)) W W2 Y) (erased (List (Nat)) K) (erased (Tl) T)
       (erased (Sw (Cons (Nat) (Succ (Succ (Succ (Zero)))) (Nil (Nat))) W (STurn K W2)) sw) (erased (Wk K W2 Y) wk)
       -> (Rd (Cons (Tk) (Tp) (Cons (Tk) (T1) W)) T Y T (Zero)))
    (many RdE : (erased (List (Tk)) W W2 Y) (erased (List (Nat)) K K2) (erased (Tl) T T2) (erased (Nat) c)
       (erased (Sw (Cons (Nat) (Succ (Succ (Succ (Zero)))) (Nil (Nat))) W (SEnd K)) sw) (erased (En K T K2 W2 T2 c) en)
       (erased (Wk K2 W2 Y) wk) -> (Rd (Cons (Tk) (Tp) (Cons (Tk) (T1) W)) T Y T2 c))))
