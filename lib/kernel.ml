type name = string

type entry_id = int

type index = int

type multiplicity = Erased | Many

type state = Comptime | Dynamic | Inacc

type discriminant = Enum | Union

type var = Free of entry_id | Bound of index

type raw = Atom of name | Sexp of raw list

module Special = struct
  type t =
    | Let
    | Def_lvl
    | Def_fns
    | Def_adts
    | Match
    | Comptime_match
    | Fn
    | Ty_ctor
    | Val_ctor
    | Matchable
    | Begin
    | Subterm_birth
    | Predates_birth
    | Comptime
    | Call
    | Ty_app
    | Val_app
    | Bundle
    | Predates_trans
    | Subterm_trans
    | Predates_via_subterm
    | Erased
    | Many
    | Colon
    | Is
    | Arrow
    | Subterm
    | Enum
    | Union
    | Tail
    | Delegate
end

type inert = Var of var | App of var * var list | Ty of former

and former =
  | Fn of fn_ty
  | Ty_ctor of tyctor_ty
  | Val_ctor of valctor_ty
  | Matchable of matchable_ty

and fn_ty = {
  level : var;
  params : param telescope;
  returns : multiplicity telescope;
}

and tyctor_ty = { indices : unit telescope }

and valctor_ty = {
  fields : multiplicity telescope;
  built_mult : multiplicity;
  built : inert;
}

and matchable_ty = {
  disc : discriminant;
  described : var;
  variants : (var * multiplicity) list;
}

and param = { mult : multiplicity; decreasing : bool }

and decl = Has_type of inert | Is of inert

and 'a telescope = 'a binder list

and 'a binder = { annot : 'a; declared : decl; binder_name : name option }

type core =
  | Inert of inert
  | Bundle of core list
  | Apply of core * core list
  | Call of call
  | Comptime of core
  | Begin of core list
  | Let of binding
  | Def_lvl of name option
  | Def_fns of fn_def list
  | Def_adts of adt_def list
  | Match of match_form
  | Comptime_match of ctor_assert
  | Birth of birth
  | Axiom of axiom

and call = {
  callee : core;
  args : core list;
  decrease : decrease;
  marker : marker;
}

and decrease =
  | Predates of core
  | Subterm of { position : int; witness : core }
  | Unrestricted

and marker = Unmarked | Tail | Delegate

and birth =
  | Subterm_of of inert * inert
  | Predates_lvl of { level : var; subject : var }

and axiom =
  | Predates_trans of core * core
  | Subterm_trans of core * core
  | Predates_via_subterm of core * core

and binding = { bound : name option; ascription : decl option; rhs : core }

and fn_def = { fn_name : name; fn_sig : fn_ty; body : core }

and adt_def = {
  adt_name : name;
  adt_sig : tyctor_ty;
  adt_disc : discriminant;
  ctors : ctor_def list;
}

and ctor_def = { ctor_name : name; ctor_sig : valctor_ty }

and match_form = {
  scrutinee : core;
  result : multiplicity telescope;
  branches : branch list;
}

and branch = { pattern : var; binds : name option list; outcome : branch_body }

and branch_body = Present of core | Absurd | Absurd_by_proof of core

and ctor_assert = { asserted : core; ctor : var; fields_bound : name option list }

type value =
  | Token
  | Data of { head : var; args : value list }
  | Fun of { def : fn_def; captured : table }
  | Ctor of var
  | Universe_of of inert
  | Matchable_val of matchable_ty
  | Level_val of int
  | Opaque
  | Special_val of Special.t
  | Macro of value
  | Datum of raw

and attr = Is_universe | Describes_special

and entry = {
  entry_name : name option;
  entry_state : state;
  entry_mult : multiplicity;
  entry_ty : inert;
  entry_is : inert option;
  stored : value option;
  attrs : attr list;
}

and table = entry array

type config = { macro_expansion_limit : int }

type request = { config : config; ambient : table; program : raw }

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
  | Macro_limit_exceeded

type checked = { final : table; elaborated : core }

type outcome = Accepted of checked | Rejected of diagnostic list

type verdict = { warnings : warning list; outcome : outcome }
