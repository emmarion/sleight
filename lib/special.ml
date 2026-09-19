type t =
  | Let | DefLvl | DefFns | DefUnique | DefAdts | ComptimeMatch | LetMatch | Unary | Distinct | OpenAdt | OpenAbsurd
  | Fn | UniqueFn | TyCtor | ValCtor | Matchable
  | Cell | SlotHolds | SlotVacant | At | Share | Match | MatchableOf | NumeralOf | LevelOf | ProveSubterm | ProvePredates | Values
  | PredatesTrans | SubtermTrans | PredatesSubterm
  | Coerce | CoercibleRefl | CoercibleSym | CoercibleTrans | CoercibleWrap | CoercibleCtor | CoercibleOf | CoercibleShare
  | Erased | Many | Unique | Colon | Is | Arrow | Subterm | Enum | Union | Tail | Delegate | Predates | Absurd | NewtypeMark | Extern | Else

let all =
  [ (Let, "let"); (DefLvl, "def-lvl"); (DefFns, "def-fns"); (DefUnique, "def-unique"); (DefAdts, "def-adts"); (ComptimeMatch, "comptime-match"); (LetMatch, "let-match"); (Unary, "unary"); (Distinct, "distinct");
    (OpenAdt, "open-adt"); (OpenAbsurd, "open-absurd");
    (Fn, "Fn"); (UniqueFn, "UniqueFn"); (TyCtor, "TyCtor"); (ValCtor, "ValCtor"); (Matchable, "Matchable");
    (Cell, "Cell"); (SlotHolds, "SlotHolds"); (SlotVacant, "SlotVacant"); (At, "at"); (Share, "share"); (Match, "match"); (MatchableOf, "matchable-of"); (NumeralOf, "numeral-of"); (LevelOf, "level-of"); (ProveSubterm, "prove-subterm");
    (ProvePredates, "prove-predates"); (Values, "values");
    (PredatesTrans, "predates-trans"); (SubtermTrans, "subterm-trans"); (PredatesSubterm, "predates-subterm");
    (Coerce, "coerce"); (CoercibleRefl, "coercible-refl"); (CoercibleSym, "coercible-sym");
    (CoercibleTrans, "coercible-trans"); (CoercibleWrap, "coercible-wrap"); (CoercibleCtor, "coercible-ctor");
    (CoercibleOf, "coercible-of"); (CoercibleShare, "coercible-share");
    (Erased, "erased"); (Many, "many"); (Unique, "unique"); (Colon, ":"); (Is, "is"); (Arrow, "->"); (Subterm, "subterm");
    (Enum, "enum"); (Union, "union"); (Tail, "tail"); (Delegate, "delegate"); (Predates, "predates");
    (Absurd, "absurd"); (NewtypeMark, "newtype"); (Extern, "extern"); (Else, "else") ]

let name s = List.assoc s all
let statements = [ Let; DefLvl; DefFns; DefUnique; DefAdts; ComptimeMatch; LetMatch; Unary; OpenAdt ]
