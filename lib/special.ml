type t =
  | Let | DefLvl | DefFns | DefUnique | DefAdts | ComptimeMatch | LetMatch | Unary | Distinct | OpenAdt | OpenAbsurd
  | Fn | UniqueFn | TyCtor | ValCtor | Matchable
  | CellAlloc | CellWrite | CellMatch | Cell | SlotOf | SlotSelf | AtFnOf | OpenAtFn | At | Share | Match | MatchableOf | NumeralOf | LevelOf | ProveSubterm | ProvePredates | Values
  | PredatesTrans | SubtermTrans | PredatesSubterm
  | Coerce | CoercibleRefl | CoercibleSym | CoercibleTrans | CoercibleWrap | CoercibleCtor | CoercibleOf | DelegateOf | CoercibleShare | DumpContext
  | Erased | Many | Unique | Colon | Is | Arrow | Subterm | Enum | Union | Tail | NoTail | Delegate | Predates | Absurd | NewtypeMark | Extern | Else

let all =
  [ (Let, "let"); (DefLvl, "def-lvl"); (DefFns, "def-fns"); (DefUnique, "def-unique"); (DefAdts, "def-adts"); (ComptimeMatch, "comptime-match"); (LetMatch, "let-match"); (Unary, "unary"); (Distinct, "distinct");
    (OpenAdt, "open-adt"); (OpenAbsurd, "open-absurd");
    (Fn, "Fn"); (UniqueFn, "UniqueFn"); (TyCtor, "TyCtor"); (ValCtor, "ValCtor"); (Matchable, "Matchable");
    (CellAlloc, "cell-alloc"); (CellWrite, "cell-write"); (CellMatch, "cell-match"); (Cell, "Cell"); (SlotOf, "slot-of"); (SlotSelf, "slot-self"); (AtFnOf, "at-fn-of"); (OpenAtFn, "open-at-fn"); (At, "at"); (Share, "share"); (Match, "match"); (MatchableOf, "matchable-of"); (NumeralOf, "numeral-of"); (LevelOf, "level-of"); (ProveSubterm, "prove-subterm");
    (ProvePredates, "prove-predates"); (Values, "values");
    (PredatesTrans, "predates-trans"); (SubtermTrans, "subterm-trans"); (PredatesSubterm, "predates-subterm");
    (Coerce, "coerce"); (CoercibleRefl, "coercible-refl"); (CoercibleSym, "coercible-sym");
    (CoercibleTrans, "coercible-trans"); (CoercibleWrap, "coercible-wrap"); (CoercibleCtor, "coercible-ctor");
    (CoercibleOf, "coercible-of"); (DelegateOf, "delegate-of"); (CoercibleShare, "coercible-share"); (DumpContext, "dump-context");
    (Erased, "erased"); (Many, "many"); (Unique, "unique"); (Colon, ":"); (Is, "is"); (Arrow, "->"); (Subterm, "subterm");
    (Enum, "enum"); (Union, "union"); (Tail, "tail"); (NoTail, "notail"); (Delegate, "delegate"); (Predates, "predates");
    (Absurd, "absurd"); (NewtypeMark, "newtype"); (Extern, "extern"); (Else, "else") ]

let name s = List.assoc s all
let statements = [ Let; DefLvl; DefFns; DefUnique; DefAdts; ComptimeMatch; LetMatch; Unary; OpenAdt; SlotSelf; OpenAtFn; DumpContext ]

let help = ref Specials_source.source

let lines kind key =
  let prefix = kind ^ " " ^ key ^ ": " and n = String.length kind + String.length key + 3 in
  List.filter_map (fun l -> if String.starts_with ~prefix l then Some (String.sub l n (String.length l - n)) else None) (String.split_on_char '\n' !help)

let hints key = String.concat "" (List.map (( ^ ) "\nhint: usage: ") (lines "usage" key))

let has_role sp = lines "role" (name sp) <> []
let role_hints sp = let n = name sp in String.concat "" (List.map (Printf.sprintf "\nhint: `%s` %s" n) (lines "role" n)) ^ hints n
let misuse sp = Printf.sprintf "malformed `%s` form%s" (name sp) (hints (name sp))
