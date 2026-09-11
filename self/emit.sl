; self/emit.sl -- OCaml extraction of the elaborated program (self/README.md; lib/extract.ml): every block of
; the store that a Const or a final value reaches becomes one let in address order, so that sharing is the
; store's; a group's block is a let rec over its members; and each final value is consumed as lib/program.ml
; would.

(def-fns _ $ many top-name : (many (Env) env) (many (Bin) x) -> (many (String) s)
  (str-cat "v" $ str-cat (bin-str x) $ str-cat "_" $ sanitize $ name-of env x))

(let (many show-fuel) 100000)

(def-fns _ $ many quoted : (many (String) s) -> (many (Rope) r)
  (rcat3 (RStr "\"") (ocaml-escape s) $ RStr "\""))

(def-fns _ $ many nat-rope : (many (Nat) n) -> (many (Rope) r)
  (RStr $ nat-str n))

(def-fns _ $ many nat-literal : (many (Nat) n) -> (many (Rope) r)
  (rcat3 (RStr "(Nat (Z.of_string \"") (nat-rope n) $ RStr "\"))"))

(def-fns _ $ many let-rope : (many (String) name) (many (Rope) e) -> (many (Rope) r)
  (rcat5 (RStr "let ") (RStr name) (RStr " = ") e $ RStr "\n"))

(def-fns _ $ many bracketed : (subterm many (List $ Rope) rs) -> (many (Rope) r)
  (rcat3 (RStr "[") (rjoin rs "; ") $ RStr "]"))

(def-fns _ $ many names-of-ids : (subterm many (List $ Bin) ids) (many (Env) env) -> (many (List $ Rope) r)
  (match many ids _
    ((Nil a) (Nil _))
    ((Cons a x rest) (Cons _ (RStr $ top-name env x) $ names-of-ids rest env))))

; An OCaml pattern binding the ids: a list pattern of their names.
(def-fns _ $ many ids-pattern : (many (List $ Bin) ids) (many (Env) env) -> (many (Rope) r)
  (bracketed $ names-of-ids ids env))

; A tuple of values as the runtime keeps it: none is U, one is bare, more a Tup.
(def-fns _ $ many tuple-rope : (many (List $ Rope) rs) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (RStr "U"))
    ((Cons a r rest)
      (match many rest _
        ((Nil b) r)
        ((Cons b r2 rest2) (rcat3 (RStr "(Tup ") (bracketed rs) $ RStr ")"))))))

; Binding the names to a value of that shape.
(def-fns _ $ many untuple-rope : (many (List $ Rope) names) (many (Rope) e) (many (Rope) body) -> (many (Rope) r)
  (match many names _
    ((Nil a) (rcat5 (RStr "(let _ = ") e (RStr " in ") body $ RStr ")"))
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (rcat5 (RStr "(let ") x (RStr " = ") (rcat3 e (RStr " in ") body) $ RStr ")"))
        ((Cons b y rest2) (rcat5 (RStr "(match ") e (rcat3 (RStr " with Tup ") (bracketed names) $ RStr " -> ") body $ RStr " | _ -> absurd ())"))))))

; Constructing a value from a constructor and the code of its many fields.
(def-fns _ $ many build-rope : (many (Ctor) c) (many (List $ Rope) args) -> (many (Rope) r)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many ext _
        ((Some a e) (rcat5 (RStr "(con_") (RStr $ ext-type-name e) (rcat3 (RStr " ") (nat-rope index) $ RStr " ") (bracketed args) $ RStr ")"))
        ((None a)
          (match many tagged _
            ((BTrue) (rcat5 (RStr "(Tag (") (nat-rope index) (RStr ", ") (bracketed args) $ RStr "))"))
            ((BFalse) (tuple-rope args))))))))

(def-fns _ $ many ctor-fn-rope : (many (Ctor) c) -> (many (Rope) r)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many ext _
        ((Some a e) (rcat5 (RStr "(Fn (con_") (RStr $ ext-type-name e) (RStr " ") (nat-rope index) $ RStr "))"))
        ((None a)
          (match many tagged _
            ((BTrue) (rcat3 (RStr "(Fn (fun args -> Tag (") (nat-rope index) $ RStr ", args)))"))
            ((BFalse) (RStr "(Fn tuple)"))))))))

(def-fns _ $ many matchable-rope : (many (Adt) adt) -> (many (Rope) r)
  (match many adt _
    ((MkAdt name tagged ctors ext)
      (match many ext _
        ((Some a e) (rcat3 (RStr "(Mat (fun _ v -> des_") (RStr $ ext-type-name e) $ RStr " v))"))
        ((None a)
          (match many tagged _
            ((BTrue) (RStr "(Mat (fun _ v -> des_tag v))"))
            ((BFalse) (RStr "(Mat (fun n v -> (0, untuple n v)))"))))))))

; The destructor a known shape reads a value through: the FFI's, the tag's, or the fields themselves.
(def-fns _ $ many des-rope : (many (Adt) adt) (many (Rope) scrut) -> (many (Rope) r)
  (match many adt _
    ((MkAdt name tagged ctors ext)
      (match many ext _
        ((Some a e) (rcat5 (RStr "(des_") (RStr $ ext-type-name e) (RStr " ") scrut $ RStr ")"))
        ((None a) (rcat3 (RStr "(des_tag ") scrut $ RStr ")"))))))

(def-fns _ $ many adt-untagged : (many (Adt) adt) -> (many (Bool) r)
  (match many adt _
    ((MkAdt name tagged ctors ext) (match many ext _ ((Some a e) (BFalse)) ((None a) (not tagged))))))

(def-fns _ $ many payload-rope : (many (Payload) p) -> (many (Rope) r)
  (match many p _
    ((PNat n) (nat-literal n))
    ((PBin b)
      (let (many n) (erased pf) $ bin-to-nat b)
      (nat-literal n))
    ((PStr s) (rcat5 (RStr "(Str (") (quoted s) (RStr ", 0, ") (nat-rope $ str-length s) $ RStr "))"))))

; ---- Names for the frames code binds: a rope per id, in step with the frames (ASSUMPTIONS 127)

(def-adts $ Names : ((List $ List $ Bin) ctx) -> Type
  enum
  (many NmNil : -> (Names (Nil (List (Bin)))))
  (many NmFrame : (erased (List $ List $ Bin) ctx) (many (List $ Bin) f) (many (List $ Rope) rs) (erased (Lockstep (Bin) (Rope) f rs) lk) (many (Names ctx) rest) -> (Names (Cons (List (Bin)) f ctx))))

(def-fns _ $ many names-get : (erased (Bin) x) (erased (List $ List $ Bin) ctx) (subterm many (Mem x ctx) p) (many (Names ctx) ns) -> (many (Rope) r)
  (match many p _
    ((MHere y f c q) (match many ns _ ((NmFrame c2 f2 rs lk rest) (let (many r) (erased sq) $ at-get _ _ _ q rs lk) r)))
    ((MThere y f c q) (match many ns _ ((NmFrame c2 f2 rs lk rest) (names-get _ _ q rest))))))

(def-fns _ $ many top-names : (subterm many (List $ Bin) ids) (many (Env) env) -> (many (List $ Rope) r) (erased (Lockstep (Bin) (Rope) ids r) lk)
  (match many ids _
    ((Nil a) (values (Nil _) (LsNil _ _)))
    ((Cons a x rest)
      (let (many rs) (erased lk) $ top-names rest env)
      (let (many r) $ RStr $ top-name env x)
      (values (Cons _ r rs) (LsCons _ _ x r rest rs lk)))))

(def-fns _ $ many push-names : (erased (List $ List $ Bin) ctx) (many (List $ Bin) ids) (many (Env) env) (many (Names ctx) ns) -> (many (Names (Cons (List (Bin)) ids ctx)) r)
  (let (many rs) (erased lk) $ top-names ids env)
  (NmFrame _ ids rs lk ns))

(def-fns _ $ many addr-rope : (erased (Nat) a) (many (Addr a) at) -> (many (Rope) r)
  (rcat (RStr "a") $ bin-rope $ addr-path _ at))

(def-fns _ $ many addr-ropes : (erased (Nat) a) (subterm many (List $ Addr a) vs) -> (many (List $ Rope) rs)
  (match many vs _
    ((Nil t) (Nil _))
    ((Cons t v rest) (Cons _ (addr-rope _ v) $ addr-ropes _ rest))))

(def-fns _ $ many const-rope : (many (Env) env) (many (Bin) x) -> (many (Rope) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store env)
  (match many (idmap-get _ x en) _
    ((Miss ht hk hm hq) (RStr "(failwith \"unbound constant\")"))
    ((Hit ht hk hm info hq)
      (match many info _
        ((MkEInfo z n m s mi me) (match many s _ ((SDyn z2) (RStr "(failwith \"a Dyn constant\")")) ((SConst z2 v) (addr-rope _ v))))))))

; The names of a group block's captured frames: an address's block by name, a group's member by projection.
(def-fns _ $ many frame-ropes : (erased (Nat) a) (erased (List $ Bin) f) (subterm many (List $ Addr a) vs) (erased (Lockstep (Bin) (Addr a) f vs) lk) -> (many (List $ Rope) rs) (erased (Lockstep (Bin) (Rope) f rs) lk2)
  (match many vs _
    ((Nil t) (match erased lk _ ((LsNil ta tb) (values (Nil _) (LsNil _ _)))))
    ((Cons t v rest)
      (match erased lk _
        ((LsCons ta tb x y xs ys p)
          (let (many rs) (erased lk2) $ frame-ropes _ _ rest p)
          (let (many r) $ addr-rope _ v)
          (values (Cons _ r rs) (LsCons _ _ x r xs rs lk2)))))))

(def-fns _ $ many member-ropes : (subterm many (List $ Bin) gids) (many (Rope) g) (many (Nat) i) -> (many (List $ Rope) rs) (erased (Lockstep (Bin) (Rope) gids rs) lk)
  (match many gids _
    ((Nil t) (values (Nil _) (LsNil _ _)))
    ((Cons t x rest)
      (let (many rs) (erased lk) $ member-ropes rest g $ Succ i)
      (let (many r) $ rcat5 (RStr "(member ") g (RStr " ") (nat-rope i) $ RStr ")")
      (values (Cons _ r rs) (LsCons _ _ x r rest rs lk)))))

(def-fns _ $ many frame-names : (erased (Nat) a) (erased (List $ List $ Bin) ctx) (subterm many (Frames a ctx) env) -> (many (Names ctx) r)
  (match many env _
    ((FrNil z) (NmNil))
    ((FrVals z c f vs lk rest)
      (let (many rs) (erased lk2) $ frame-ropes _ _ vs lk)
      (NmFrame _ f rs lk2 $ frame-names _ _ rest))
    ((FrGroup z c gids g rest)
      (let (many rs) (erased lk2) $ member-ropes gids (addr-rope _ g) 0)
      (NmFrame _ gids rs lk2 $ frame-names _ _ rest))))

; ---- Code and blocks as OCaml; every piece recurses on the piece it writes.

(def-fns _
  (many emit-code : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (Env) env) (many (Names ctx) ns) -> (many (Rope) r)
    (match many code _
      ((CVar c0 x p) (names-get _ _ p ns))
      ((CConst c0 x) (const-rope env x))
      ((CValue c0 v) (block-rope _ v env))
      ((CErased c0 ms2) (RStr "U"))
      ((CValues c0 ms2 cs pk) (tuple-rope $ emit-codes _ cs env ns))
      ((CApp c0 ms2 f args cc) (rcat5 (RStr "(app ") (emit-code _ _ f env ns) (RStr " ") (bracketed $ emit-codes _ args env ns) $ RStr ")"))
      ((CLet c0 ms2 ns2 ids pk rhs rest) (untuple-rope (names-of-ids ids env) (emit-code _ _ rhs env ns) $ emit-code _ _ rest env $ push-names _ ids env ns))
      ((CLetRec c0 ns2 gids g rest)
        (match many g _
          ((MkGroup c1 ids fns lk)
            (rcat5 (RStr "(let rec ") (emit-group _ _ fns env $ push-names _ ids env ns) (RStr " in ") (emit-code _ _ rest env $ push-names _ ids env ns) $ RStr ")"))))
      ((CMatch c0 ns2 scrut shape branches dfl)
        (let (many sr) $ emit-code _ _ scrut env ns)
        (let (many (Nat) arity) $ match many branches _ ((Nil a) 0) ((Cons a b rest) (match many b (((Nat) n)) ((MkBranch c1 n0 d ids body) (list-length _ ids)))))
        (let (many (Rope) dr) (match many dfl _ ((None a) (RStr "absurd ()")) ((Some a d) (emit-code _ _ d env $ push-names _ (Nil _) env ns))))
        (let (many fallthrough) $ rcat3 (RStr " | _ -> ") dr $ RStr ")")
        (let (many (Bool) untagged) $ match many shape _ ((ShKnown c1 adt) (adt-untagged adt)) ((ShNone c1) (BTrue)) ((ShHeld c1 mc t) (BFalse)))
        (match many untagged _
          ((BTrue)
            (match many branches _
              ((Nil a) (rcat3 (RStr "(") dr $ RStr ")"))
              ((Cons a b rest)
                (match many b _
                  ((MkBranch c1 n0 d ids body) (untuple-rope (names-of-ids ids env) sr $ emit-code _ _ body env $ push-names _ ids env ns))))))
          ((BFalse)
            (match many shape _
              ((ShKnown c1 adt) (rcat4 (RStr "(match ") (des-rope adt sr) (rcat (RStr " with ") $ emit-branches _ _ branches env ns $ BTrue) fallthrough))
              ((ShHeld c1 mcode tags) (rcat5 (RStr "(match (app_mat ") (emit-code _ _ mcode env ns) (rcat4 (RStr " ") (nat-rope arity) (RStr " ") sr) (rcat (RStr ") with ") $ emit-branches _ _ branches env ns tags) fallthrough))
              ((ShNone c1) (rcat3 (RStr "(") dr $ RStr ")"))))))
      ((CAbsurd c0 ms2) (RStr "(absurd ())"))
      ((CError c0 ms2 m) (rcat3 (RStr "(failwith ") (quoted m) $ RStr ")"))))

  (many emit-codes : (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Env) env) (many (Names ctx) ns) -> (many (List $ Rope) rs)
    (match many cs _
      ((Nil a) (Nil _))
      ((Cons a c rest) (Cons _ (emit-code _ _ c env ns) $ emit-codes _ rest env ns))))

  (many emit-branches : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns2) (subterm many (List $ Branch ctx ns2) bs) (many (Env) env) (many (Names ctx) ns) (many (Bool) tags) -> (many (Rope) r)
    (match many bs _
      ((Nil a) (REmpty))
      ((Cons a b rest)
        (match many b _
          ((MkBranch c1 n0 d ids body)
            (let (many (Rope) disc) $ match many tags _ ((BTrue) (nat-rope d)) ((BFalse) (RStr "_")))
            (rcat5 (RStr "| (") disc (rcat3 (RStr ", ") (ids-pattern ids env) $ RStr ") -> ") (emit-code _ _ body env $ push-names _ ids env ns) $ emit-branches _ _ rest env ns tags))))))

  ; The definitions of a group, joined by and, each named by its entry.
  (many emit-group : (erased (List $ Bin) gids) (erased (List $ List $ Bin) ctx) (subterm many (List $ Pair (Bin) $ Func gids ctx) fns) (many (Env) env) (many (Names (Cons (List (Bin)) gids ctx)) ns) -> (many (Rope) r)
    (match many fns _
      ((Nil a) (REmpty))
      ((Cons a p rest)
        (match many p _
          ((MkPair x y id fn)
            (let (many (Rope) sep) $ match many rest _ ((Nil b) (REmpty)) ((Cons b q rest2) (RStr "\nand ")))
            (rcat5 (RStr $ top-name env id) (RStr " = ") (emit-fn _ _ fn env ns) sep $ emit-group _ _ rest env ns))))))

  (many emit-fn : (erased (List $ Bin) gids) (erased (List $ List $ Bin) ctx) (subterm many (Func gids ctx) fn) (many (Env) env) (many (Names (Cons (List (Bin)) gids ctx)) ns) -> (many (Rope) r)
    (match many fn _
      ((MkFunc g c rets name id params body impl top)
        (match many impl _
          ((Some a se) (match many se _ ((MkSomeExtern n e) (rcat (RStr "Fn ext_") $ RStr $ sanitize $ ext-name _ e))))
          ((None a) (rcat5 (RStr "Fn (fun args -> match args with ") (ids-pattern params env) (RStr " -> ") (emit-code _ _ body env $ push-names _ params env ns) $ RStr " | _ -> absurd ())"))))))

  ; A block as one OCaml value, its addresses by name; a group's block is its members' let rec over the
  ; names of the frames it closed over, packed as a tuple a member projects from.
  (many block-rope : (erased (Nat) a) (subterm many (Block a) b) (many (Env) env) -> (many (Rope) r)
    (match many b _
      ((BTag z tag fields) (rcat5 (RStr "(Tag (") (nat-rope tag) (RStr ", ") (bracketed $ addr-ropes _ fields) $ RStr "))"))
      ((BTup z fields) (tuple-rope $ addr-ropes _ fields))
      ((BExt z p) (payload-rope p))
      ((BCtorFn z c) (ctor-fn-rope c))
      ((BMat z adt) (matchable-rope adt))
      ((BGroup z gids ctx g env2)
        (match many g _
          ((MkGroup c1 ids fns lk)
            (rcat5 (RStr "(let rec ") (emit-group _ _ fns env $ push-names _ ids env $ frame-names _ _ env2) (RStr " in ") (tuple-rope $ names-of-ids ids env) $ RStr ")"))))
      ((BFn z g i) (rcat5 (RStr "(member ") (addr-rope _ g) (RStr " ") (nat-rope i) $ RStr ")"))
      ((BToken z) (RStr "U"))
      ((BError z m) (rcat3 (RStr "(failwith ") (quoted m) $ RStr ")")))))

; ---- The walk over the store: what a Const or a final reaches is marked from the newest address down,
; each block's addresses being below it, and then written from the oldest up.

(def-fns _ $ many mark : (erased (Nat) a) (many (Addr a) at) (many (IdMap $ Unit) marks) -> (many (IdMap $ Unit) r)
  (idmap-set _ (addr-path _ at) (MkUnit) marks))

(def-fns _ $ many marked : (erased (Nat) a) (many (Addr a) at) (many (IdMap $ Unit) marks) -> (many (Bool) r)
  (idmap-mem _ (addr-path _ at) marks))

(def-fns _ $ many mark-addrs : (erased (Nat) a) (subterm many (List $ Addr a) vs) (many (IdMap $ Unit) marks) -> (many (IdMap $ Unit) r)
  (match many vs _
    ((Nil t) marks)
    ((Cons t v rest) (mark-addrs _ rest $ mark _ v marks))))

(def-fns _ $ many mark-frames : (erased (Nat) a) (erased (List $ List $ Bin) ctx) (subterm many (Frames a ctx) env) (many (IdMap $ Unit) marks) -> (many (IdMap $ Unit) r)
  (match many env _
    ((FrNil z) marks)
    ((FrVals z c f vs lk rest) (mark-frames _ _ rest $ mark-addrs _ vs marks))
    ((FrGroup z c gids g rest) (mark-frames _ _ rest $ mark _ g marks))))

(def-fns _ $ many mark-entries : (erased (Nat) hs) (subterm many (IdMap $ EInfo hs) en) (many (IdMap $ Unit) marks) -> (many (IdMap $ Unit) r)
  (match many en _
    ((MEmpty t) marks)
    ((MNode t here one two)
      (let (many (IdMap $ Unit) marks2)
        (match many here _
          ((None u) marks)
          ((Some u info) (match many info (((IdMap $ Unit) m)) ((MkEInfo z n m s mi me) (match many s (((IdMap $ Unit) m)) ((SDyn z2) marks) ((SConst z2 v) (mark _ v marks))))))))
      (mark-entries _ two $ mark-entries _ one marks2))))

(def-fns _ $ many mark-finals : (erased (Nat) hs) (subterm many (List $ Pair (Addr hs) $ Term) fs) (many (IdMap $ Unit) marks) -> (many (IdMap $ Unit) r)
  (match many fs _
    ((Nil t) marks)
    ((Cons t p rest) (match many p _ ((MkPair x y v ty) (mark-finals _ rest $ mark _ v marks))))))

(def-fns _ $ many mark-pass : (erased (Nat) hs) (many (Heap Block hs) hp) (subterm many (List $ Addr hs) newest) (many (IdMap $ Unit) marks) -> (many (IdMap $ Unit) r)
  (match many newest _
    ((Nil t) marks)
    ((Cons t at rest)
      (let (many (IdMap $ Unit) marks2)
        (match many (marked _ at marks) _
          ((BFalse) marks)
          ((BTrue)
            (let (erased a) (erased lt) (many b) $ deref Block _ hp at)
            (match many b (((IdMap $ Unit) m))
              ((BTag z tag fields) (mark-addrs _ fields marks))
              ((BTup z fields) (mark-addrs _ fields marks))
              ((BFn z g i) (mark _ g marks))
              ((BGroup z gids ctx g env) (mark-frames _ _ env marks))
              (else marks)))))
      (mark-pass _ hp rest marks2))))

(def-fns _ $ many emit-blocks : (erased (Nat) hs) (many (Heap Block hs) hp) (subterm many (List $ Addr hs) oldest) (many (IdMap $ Unit) marks) (many (Env) env) -> (many (Rope) r)
  (match many oldest _
    ((Nil t) (REmpty))
    ((Cons t at rest)
      (let (many (Rope) this)
        (match many (marked _ at marks) _
          ((BFalse) (REmpty))
          ((BTrue)
            (let (erased a) (erased lt) (many b) $ deref Block _ hp at)
            (rcat5 (RStr "let ") (addr-rope _ at) (RStr " = ") (block-rope _ b env) $ RStr "\n"))))
      (rcat this $ emit-blocks _ hp rest marks env))))

; ---- Finals (lib/program.ml): what the driver does with a file's final value

(def-adts $ Final : -> Type
  enum
  (many FMain : -> (Final))
  (many FIo : -> (Final))
  (many FThunk : (many (Term) ty) -> (Final))
  (many FPlain : -> (Final)))

(def-fns _ $ many is-string-type : (many (Env) env) (many (Term) ty) -> (many (Bool) r)
  (match many (type-head env ty) _
    ((None a) (BFalse))
    ((Some a t) (str-eq (name-of env t) "String"))))

(def-fns _ $ many classify-final : (many (Env) env) (many (Term) ty) -> (many (Final) f)
  (match many (canon-env env ty) _
    ((TFn lv ps rs)
      (match many ps _
        ((Nil a)
          (match many rs _
            ((Cons b r more)
              (match many more _
                ((Nil c) (match many r _ ((MkEntry n s m sg) (match many m _ ((Many) (FThunk $ sg-term sg)) ((Erased) (FPlain))))))
                ((Cons c r2 more2) (FPlain))))
            ((Nil b) (FPlain))))
        ((Cons a p more)
          (match many more _
            ((Cons b p2 more2) (FPlain))
            ((Nil b)
              (match many rs _
                ((Nil c) (FPlain))
                ((Cons c r more3)
                  (match many more3 _
                    ((Cons d r2 more4) (FPlain))
                    ((Nil d)
                      (match many (and (is-string-type env $ sg-term $ entry-sg p)
                                    (and (is-string-type env $ sg-term $ entry-sg r)
                                      $ and (mult-is-many $ entry-mult p) $ mult-is-many $ entry-mult r)) _
                        ((BTrue) (FMain))
                        ((BFalse) (FPlain))))))))))))
    ((TApp h args)
      (match many (type-head env ty) _
        ((None a) (FPlain))
        ((Some a t) (match many (str-cmp (name-of env t) "IO") _ ((CEq eq-t eq-r eq-x) (FIo)) (else (FPlain)))))) (else (FPlain))))

; ---- A printer per type for a final function's result (lib/extract.ml's show): each constructor's return
; type is unified with the type to find its many fields' types, as entering a branch does.

(def-adts $ ShowMemo : -> Type
  enum
  (many MkShowMemo : (many (Bin) fresh) (many (Nat) count) (many (List $ Pair (Term) $ String) known) (many (List $ Rope) defs) -> (ShowMemo)))

(def-fns _ $ many memo-find : (subterm many (List $ Pair (Term) $ String) known) (many (Env) env) (many (Term) ty) -> (many (Maybe $ String) r)
  (match many known _
    ((Nil a) (None _))
    ((Cons a p rest)
      (match many p _
        ((MkPair x y t name)
          (match many (term-eq t ty) _
            ((BTrue) (Some _ name))
            ((BFalse) (memo-find rest env ty))))))))

(def-fns _ $ many spaced : (subterm many (List $ Rope) parts) -> (many (Rope) r)
  (match many parts _
    ((Nil a) (RStr "\"\""))
    ((Cons a p rest)
      (match many rest _
        ((Nil b) p)
        ((Cons b q rest2) (rcat3 p (RStr " ^ \" \" ^ ") $ spaced rest))))))

(def-fns _ $ many field-names : (subterm many (Nat) n) (many (Nat) i) -> (many (List $ Rope) r)
  (match many n _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ (RStr $ str-cat "f" $ nat-str i) $ field-names k $ Succ i))))

(def-fns _
  (many show-type : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty0) (many (ShowMemo) memo) -> (many (ShowMemo) memo2) (many (String) name)
    (match many fuel _
      ((Zero) (values memo "show_any"))
      ((Succ k)
        (let (many ty) $ canon-env env ty0)
        (match many memo _
          ((MkShowMemo fresh count known defs)
            (let (many key) $ mapv ty (OpWild fresh) 0)
            (match many (memo-find known env key) _
              ((Some a name) (values memo name))
              ((None a)
                (let (many name) $ str-cat "show_" $ nat-str count)
                (let (many memo1) $ MkShowMemo fresh (Succ count) (Cons _ (MkPair _ _ key name) known) defs)
                (let (many (ShowMemo) memo2) (many (Rope) body)
                  (match many ty _
                    ((TApp h args)
                      (match many (type-head env ty) (((ShowMemo) m) ((Rope) r))
                        ((None b) (values memo1 $ RStr "\"?\""))
                        ((Some b tid)
                          (let (many envf) (many foundm) $ find-matchable env tid)
                          (match many foundm (((ShowMemo) m) ((Rope) r))
                            ((None c) (values memo1 $ RStr "\"?\""))
                            ((Some c info)
                              (match many info (((ShowMemo) m) ((Rope) r))
                                ((MkMatchInfo mid disc mctors rank)
                                  (match many (adt-of env mid) (((ShowMemo) m) ((Rope) r))
                                    ((None d) (values memo1 $ RStr "\"?\""))
                                    ((Some d adt)
                                      (match many adt (((ShowMemo) m) ((Rope) r))
                                        ((MkAdt aname tagged ctors ext)
                                          (let (many untagged) $ adt-untagged adt)
                                          (let (many memo3) (many arms) $ show-arms k env ty ctors memo1 untagged)
                                          (match many untagged (((ShowMemo) m) ((Rope) r))
                                            ((BTrue) (values memo3 arms))
                                            ((BFalse) (values memo3 $ rcat3 (rcat (RStr "match ") $ des-rope adt $ RStr "v") (rcat (RStr " with ") arms) $ RStr " | _ -> \"?\""))))))))))))))
                    ((TFn l ps rs) (values memo1 $ RStr "\"<function ?>\""))
                    ((TValCtor ps r) (values memo1 $ RStr "\"<constructor ?>\"")) (else (values memo1 $ RStr "\"?\""))))
                (match many memo2 _
                  ((MkShowMemo fresh2 count2 known2 defs2)
                    (values (MkShowMemo fresh2 count2 known2 $ Cons _ (rcat4 (RStr name) (RStr " (v : v) : string = ") body $ REmpty) defs2) name))))))))))

  ; One arm per non-phantom constructor whose return type the instance does not refute, its fields shown
  ; only then, as the reference's exception skips them; an untagged type has one arm reading the fields as they stand.
  (many show-arms : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty) (many (List $ Ctor) ctors) (many (ShowMemo) memo) (many (Bool) untagged) -> (many (ShowMemo) memo2) (many (Rope) arms)
    (match many fuel _
      ((Zero) (values memo $ REmpty))
      ((Succ k)
        (match many ctors _
          ((Nil a) (values memo $ REmpty))
          ((Cons a c rest)
            (match many c _
              ((MkCtor cname cid index arity tagged ext)
                (let (many ctele) (many ret) $ ctor-type env cid)
                (let (many envb) (many fids) (erased lock) $ open-tele ctele env (None _) (None _) (Nil _) $ BFalse)
                (let (many (Env) envb2) (many (Bool) live)
                  (match many (unify-env envb (instantiate (tvars-rev fids $ Nil _) ret) ty $ BTrue) _
                    ((UOk e2) (values e2 $ BTrue))
                    ((UContra msg) (values envb $ BFalse))))
                (let (many (ShowMemo) memo2) (many (List $ Rope) shown)
                  (match many live _
                    ((BTrue) (show-fields k envb2 (non-erased fids envb2) memo 0))
                    ((BFalse) (values memo $ Nil _))))
                (let (many fnames) $ field-names arity 0)
                (let (many (Rope) text)
                  (match many untagged _
                    ((BTrue) (match many shown (((Rope) r)) ((Nil b) (RStr "\"_\"")) ((Cons b s more) (match many more (((Rope) r)) ((Nil d) s) ((Cons d s2 more2) (rcat3 (RStr "\"(\" ^ ") (spaced shown) $ RStr " ^ \")\""))))))
                    ((BFalse) (rcat3 (RStr "\"(\" ^ ") (spaced $ Cons _ (quoted cname) shown) $ RStr " ^ \")\""))))
                (let (many (Rope) arm)
                  (match many untagged _
                    ((BTrue) (untuple-rope fnames (RStr "v") text))
                    ((BFalse) (rcat5 (RStr "| (") (nat-rope index) (rcat3 (RStr ", ") (bracketed fnames) $ RStr ") -> ") text $ REmpty))))
                (let (many memo3) (many more) $ show-arms k env ty rest memo2 untagged)
                (values memo3 $ match many live (((Rope) r)) ((BTrue) (rcat3 arm (RStr " ") more)) ((BFalse) more)))))))))

  (many show-fields : (subterm many (Nat) fuel) (many (Env) env) (many (List $ Bin) fids) (many (ShowMemo) memo) (many (Nat) i) -> (many (ShowMemo) memo2) (many (List $ Rope) shown)
    (match many fuel _
      ((Zero) (values memo $ Nil _))
      ((Succ k)
        (match many fids _
          ((Nil a) (values memo $ Nil _))
          ((Cons a x rest)
            (let (many memo2) (many name) $ show-type k env (type-of env x) memo)
            (let (many memo3) (many more) $ show-fields k env rest memo2 $ Succ i)
            (values memo3 $ Cons _ (rcat3 (RStr name) (RStr " f") $ nat-rope i) more)))))))

(def-fns _ $ many show-defs : (many (ShowMemo) memo) -> (many (Rope) r)
  (match many memo _
    ((MkShowMemo fresh count known defs)
      (match many defs _
        ((Nil a) (REmpty))
        ((Cons a d rest) (rcat3 (RStr "let rec ") (rjoin (list-rev _ defs) "\nand ") $ RStr "\n"))))))

(def-fns _ $ many fn-name-at : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Addr hs) v) -> (many (Maybe $ String) r)
  (let (erased a) (erased lt) (many b) $ deref Block _ hp v)
  (match many b _
    ((BFn z g i)
      (let (erased a2) (erased lt2) (many gb) $ deref Block _ hp $ addr-weaken _ _ (lt-weaken _ _ lt) g)
      (match many gb _
        ((BGroup z2 gids ctx grp env2)
          (match many grp _
            ((MkGroup c ids fns lk)
              (match many (list-nth _ fns i) _
                ((NthHit nt nl ni p np) (match many p _ ((MkPair x y id fn) (Some _ $ func-name _ _ fn))))
                ((NthMiss nt nl ni np) (None _))))))
        (else (None $ String))))
    (else (None $ String))))

(def-fns _ $ many final-rope : (many (Env) env) (erased (Nat) hs) (many (Heap Block hs) hp) (many (Addr hs) v) (many (Term) ty) -> (many (Rope) r)
  (let (many vr) $ addr-rope _ v)
  (match many (classify-final env ty) _
    ((FMain) (rcat3 (RStr "let () = run_main ") vr $ RStr "\n"))
    ((FIo) (rcat3 (RStr "let () = exit (run_io ") vr $ RStr ")\n"))
    ((FThunk t)
      (let (many memo) (many name) $ show-type show-fuel env t $ MkShowMemo (env-fresh-bound env) 0 (Nil _) $ Nil _)
      (rcat5 (show-defs memo) (RStr "let () = print_endline (") (RStr name) (rcat3 (RStr " (app ") vr $ RStr " []))") $ RStr "\n"))
    ((FPlain)
      (match many (fn-name-at _ hp v) _
        ((Some a fname) (rcat3 (RStr "let () = print_endline ") (quoted $ str-cat3 "<function " fname ">") $ RStr "\n"))
        ((None a)
          (let (many memo) (many name) $ show-type show-fuel env ty $ MkShowMemo (env-fresh-bound env) 0 (Nil _) $ Nil _)
          (rcat5 (show-defs memo) (RStr "let () = print_endline (") (RStr name) (rcat3 (RStr " ") vr $ RStr ")") $ RStr "\n"))))))

(def-fns _ $ many emit-finals : (erased (Nat) hs) (many (Heap Block hs) hp) (subterm many (List $ Pair (Addr hs) $ Term) fs) (many (Env) env) -> (many (Rope) r)
  (match many fs _
    ((Nil t) (REmpty))
    ((Cons t p rest) (match many p _ ((MkPair x y v ty) (rcat (final-rope env _ hp v ty) $ emit-finals _ hp rest env))))))

(def-fns _ $ many emit-program : (many (Env) env) -> (many (Rope) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store env)
  (let (many addrs) $ heap-addrs Block _ hp)
  (let (many marks) $ mark-pass _ hp (list-rev _ addrs) $ mark-finals _ fi $ mark-entries _ en $ MEmpty _)
  (rcat3 runtime-header (emit-blocks _ hp addrs marks env) $ emit-finals _ hp (list-rev _ fi) env))
