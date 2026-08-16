type name = string

type entry_id = int

type index = int

type obligation_id = int

type multiplicity = Erased | Many

type state = Comptime | Dynamic | Inacc

type discriminant = Enum | Union

type var = Free of entry_id | Bound of index

type inert = Var of var | App of var * var list | Ty of former

and former =
  | Fn of fn_ty
  | Ty_ctor of tyctor_ty
  | Val_ctor of valctor_ty
  | Matchable of matchable_ty

and fn_ty = {
  level : var;
  params : param telescope;
  returns : slot telescope;
}

and tyctor_ty = { indices : decl telescope }

and valctor_ty = {
  fields : slot telescope;
  built_mult : multiplicity;
  built : inert;
}

and matchable_ty = {
  disc : discriminant;
  described : var;
  variants : (var * multiplicity) list;
}

and decl = Has_type of inert | Is of inert

and slot = { mult : multiplicity; declared : decl }

and param = { slot : slot; decreasing : bool }

and 'a telescope = 'a binder list

and 'a binder = { site : 'a; binder_name : name option }

type complete

type elided

type _ core =
  | Elided : elided core
  | Inert : inert -> 'e core
  | Bundle : 'e core list -> 'e core
  | Apply : 'e core * 'e core list -> 'e core
  | Call : 'e call -> 'e core
  | Comptime : 'e body -> 'e core
  | Let : 'e binding -> 'e core
  | Def_lvl : name option -> 'e core
  | Def_fns : 'e fn_def list -> 'e core
  | Def_adts : adt_def list -> 'e core
  | Match : 'e match_form -> 'e core
  | Comptime_match : 'e ctor_assert -> 'e core
  | Birth : birth -> 'e core
  | Axiom : 'e axiom -> 'e core

and 'e body = 'e core list

and 'e call = {
  callee : 'e core;
  args : 'e core list;
  decrease : 'e decrease;
  marker : marker;
}

and 'e decrease =
  | Predates of 'e core
  | Subterm of { position : int; witness : 'e core }
  | Unrestricted

and marker = Unmarked | Tail | Delegate

and birth =
  | Subterm_of of inert * inert
  | Predates_lvl of { level : var; subject : var }

and 'e axiom =
  | Predates_trans of 'e core * 'e core
  | Subterm_trans of 'e core * 'e core
  | Predates_via_subterm of 'e core * 'e core

and 'e binding = { bound : decl option telescope; rhs : 'e core }

and 'e fn_def = { fn_name : name; fn_sig : fn_ty; body : 'e body }

and adt_def = {
  adt_name : name;
  adt_sig : tyctor_ty;
  adt_disc : discriminant;
  ctors : ctor_def list;
}

and ctor_def = { ctor_name : name; ctor_sig : valctor_ty }

and 'e match_form = {
  scrutinee : 'e core;
  result : slot telescope;
  branches : 'e branch list;
}

and 'e branch = {
  pattern : var;
  binds : name option list;
  outcome : 'e branch_body;
}

and 'e branch_body =
  | Present of 'e body
  | Absurd
  | Absurd_by_proof of 'e body

and 'e ctor_assert = {
  asserted : 'e core;
  ctor : var;
  fields_bound : name option list;
}

type value =
  | Token
  | Data of { head : var; args : value list }
  | Fun of { defn : entry_id; captured : table }
  | Ctor of var
  | Ty_val of inert
  | Matchable_val of matchable_ty
  | Level_val of int
  | Opaque

and attr = Is_universe | Describes_special

and entry = {
  entry_name : name option;
  entry_state : state;
  entry_mult : multiplicity;
  entry_ty : inert;
  entry_is : inert option;
  definition : complete core option;
  stored : value option;
  attrs : attr list;
}

and table = entry array

type ask =
  | Check of { term : complete body; expects : slot telescope option }
  | Evaluate of { term : complete body }
  | Admit of { obligation : obligation_id; results : value list }
  | Abandon of obligation_id
  | Infer of complete core
  | Canonicalize of inert

type warning = Phantom_with_many_field of { ctor : name; field : int }

type diagnostic =
  | Head_not_applicable
  | Occurs_check of var
  | Distinct_ctors of var * var
  | Not_canonically_equal of inert * inert
  | Not_comptime of var
  | Inaccessible of var
  | Erasure_violation of var
  | No_decrease
  | Not_a_strict_subterm of inert * inert
  | Level_not_prior of var
  | Tail_not_honorable
  | Ambiguous_matchable of var
  | Too_many_real_branches
  | Wrong_discriminant of var
  | Unrestricted_outside_comptime
  | Unknown_obligation of obligation_id
  | Result_arity_mismatch of { expected : int; admitted : int }
  | Value_not_of_type of value * inert
  | Value_should_be_elided of index

type reply =
  | Accepted of {
      table : table;
      results : entry_id list;
      warnings : warning list;
    }
  | Runnable of {
      obligation : obligation_id;
      code : elided body;
      expects : slot telescope;
    }
  | Inferred of slot telescope
  | Canonical of inert
  | Refused of diagnostic list

type session = {
  scope : table;
  outstanding : (obligation_id * slot telescope) list;
}
