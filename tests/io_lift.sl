; stdin: a
; stdin: bb
; expect: starting
; expect: > bb
; exit: 3
; Two libraries at two levels embedded in a program at a third, at no runtime cost: lift2 mints the program's
; level B and returns, erased, each program at (Program B) and the proof that coerces to it. The erased walk
; gives each continuation a level-B delegate, whose coercibility coercible-ctor lifts through the step; every
; proof is minted inside, after B, so the caller supplies levels and values only. A program and its
; continuations are unique, so the proofs' sides are (Unique) and a delegate is a def-unique; the many-labelled
; exit code keeps (Shared).
(def-lvl proof-lvl)
(def-lvl lift-lvl)
(let ((erased pl)) (prove-predates proof-lvl lift-lvl))

(def-fns lift-lvl $ (erased lift2 : (erased (Level) L1) (erased (Level) L2) (unique (Program L1) io1) (unique (Program L2) io2) ->
    (erased (Level) B) (erased (Program B) o1) (erased (Program B) o2)
    (erased (Coercible (Unique) (Program L1) io1 (Unique) (Program B) o1) q1) (erased (Coercible (Unique) (Program L2) io2 (Unique) (Program B) o2) q2))
  (def-lvl B)
  (let ((erased p1)) (prove-predates L1 B))
  (let ((erased p2)) (prove-predates L2 B))
  (def-fns proof-lvl $ (erased lift-proof : (erased (Level) A) (erased (Predates (Level) A B) ab) (subterm unique (Program A) io) ->
      (erased (Program B) out) (erased (Coercible (Unique) (Program B) out (Unique) (Program A) io) p))
    (def-fns proof-lvl $ (erased lift-fn : (subterm unique (UniqueFn A (unique (World) w) -> (unique (World) w2 at w) (unique (Program A) next)) k) ->
        (erased (UniqueFn B (unique (World) w) -> (unique (World) w2 at w) (unique (Program B) next)) o)
        (erased (Coercible (Unique) (UniqueFn B (unique (World) w) -> (unique (World) w2 at w) (unique (Program B) next)) o
                           (Unique) (UniqueFn A (unique (World) w) -> (unique (World) w2 at w) (unique (Program A) next)) k) p))
      (def-unique B $ (unique o at k : (unique (World) w) -> (unique (World) w2 at w) (unique (Program B) next))
        (let ((unique w2) (unique r)) (delegate (k (predates ab) w)))
        (let ((erased o2) (erased q)) (lift-proof A ab r))
        (values w2 (coerce r (coercible-sym q))))
      (values o (coercible-of (delegate-of o))))
    (let-match erased io (Continue l k) ((Exit l c) (values (Exit B c) (coercible-ctor (Unique) Exit B A (coercible-refl (Shared) c)))))
    (let ((erased o) (erased q)) (lift-fn k))
    (values (Continue B o) (coercible-ctor (Unique) Continue B A q)))
  (let ((erased x1) (erased q1)) (lift-proof L1 p1 io1))
  (let ((erased x2) (erased q2)) (lift-proof L2 p2 io2))
  (values B x1 x2 (coercible-sym q1) (coercible-sym q2)))

(def-lvl A10)
(def-lvl A1)
(let ((many d3)) (lt-dec 3 u8-modulus))
(comptime-match many d3 (Yes za3 zb3 zp3))
(let ((many code3)) (MkU8 3 zp3))
(def-fns A10 $ (many lib-echo : (unique (World) w) -> (unique (World) w2 at w) (unique (Program A1) p))
  (let ((unique w1) (many line)) (world-do _ w (ReadLine)))
  (let-match many line (Some a s) ((None a) (values w1 (Exit A1 code3))))
  (let ((unique w3) (many _)) (world-do _ w1 (WriteOut (str-append "> " (str-append s "\n")))))
  (def-unique A1 $ (unique again : (unique (World) v) -> (unique (World) v2 at v) (unique (Program A1) p)) (lib-echo v))
  (values w3 (Continue A1 again)))
(def-unique A1 $ (unique echo-start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program A1) p)) (lib-echo w))

(def-lvl A2)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(def-unique A2 $ (unique banner : (unique (World) w) -> (unique (World) w2 at w) (unique (Program A2) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteErr $ match many args (((String) _)) ((Nil a) "no args\n") ((Cons a x rest) x))))
  (values w2 (Exit A2 code0)))

(let ((unique echo-a1)) (Continue A1 echo-start))
(let ((unique banner-a2)) (Continue A2 banner))
(let ((erased B) (erased e) (erased b) (erased qe) (erased qb)) (lift2 A1 A2 echo-a1 banner-a2))
(def-unique B $ (unique user-start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program B) p))
  (let ((unique w1) (many line)) (world-do _ w (ReadLine)))
  (let-match many line (Some a s) ((None a) (values w1 (coerce banner-a2 qb))))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut "starting\n")))
  (values w2 (coerce echo-a1 qe)))

(Continue B user-start)
