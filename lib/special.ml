type t =
  | Let | DefLvl | DefFns | DefAdts | ComptimeMatch
  | Fn | TyCtor | ValCtor | Matchable | Newtype
  | Match | MatchableOf | NewtypeOf | NumeralOf | LevelOf | ProveSubterm | ProvePredates | Values
  | PredatesTrans | SubtermTrans | PredatesSubterm
  | Coerce | CoercibleRefl | CoercibleSym | CoercibleTrans | CoercibleWrap | CoercibleCtor | CoercibleOf
  | Erased | Many | Colon | Is | Arrow | Subterm | Enum | Union | Tail | Delegate | Predates | Absurd | NewtypeMark | Extern

let all =
  [ (Let, "let"); (DefLvl, "def-lvl"); (DefFns, "def-fns"); (DefAdts, "def-adts"); (ComptimeMatch, "comptime-match");
    (Fn, "Fn"); (TyCtor, "TyCtor"); (ValCtor, "ValCtor"); (Matchable, "Matchable"); (Newtype, "Newtype");
    (Match, "match"); (MatchableOf, "matchable-of"); (NewtypeOf, "newtype-of"); (NumeralOf, "numeral-of"); (LevelOf, "level-of"); (ProveSubterm, "prove-subterm");
    (ProvePredates, "prove-predates"); (Values, "values");
    (PredatesTrans, "predates-trans"); (SubtermTrans, "subterm-trans"); (PredatesSubterm, "predates-subterm");
    (Coerce, "coerce"); (CoercibleRefl, "coercible-refl"); (CoercibleSym, "coercible-sym");
    (CoercibleTrans, "coercible-trans"); (CoercibleWrap, "coercible-wrap"); (CoercibleCtor, "coercible-ctor");
    (CoercibleOf, "coercible-of");
    (Erased, "erased"); (Many, "many"); (Colon, ":"); (Is, "is"); (Arrow, "->"); (Subterm, "subterm");
    (Enum, "enum"); (Union, "union"); (Tail, "tail"); (Delegate, "delegate"); (Predates, "predates");
    (Absurd, "absurd"); (NewtypeMark, "newtype"); (Extern, "extern") ]

let name s = List.assoc s all
let statements = [ Let; DefLvl; DefFns; DefAdts; ComptimeMatch ]

(* Value-constructor entry id of each special's variant in the [Special] ADT. *)
let table : (Term.id, t) Hashtbl.t = Hashtbl.create 64
