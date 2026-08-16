type var = int
type ix = int
type name = string option

type mult = Erased | Many
type disc = Enum | Union

type ref_ =
  | Free of var
  | Bound of ix

type tyexpr =
  | Ref of ref_
  | App of ref_ * tyexpr list
  | Fn of ref_ * fn_param list * fn_ret list
  | TyCtor of entry_sig list
  | ValCtor of valctor_field list * ref_ * tyexpr list
  | Matchable of disc * ref_ * (mult * ref_) list

and entry_sig =
  | Ty of tyexpr
  | Is of tyexpr

and fn_param = { fp_subterm : bool; fp_mult : mult; fp_sig : entry_sig }
and fn_ret = { fr_mult : mult; fr_sig : entry_sig }
and valctor_field = { vf_mult : mult; vf_sig : entry_sig }

type decrease =
  | Predates of var
  | Subterm of int * var
  | NoProof

type cc = Plain | Tail | Delegate

type expr = { stmts : stmt list; result : (var * mult option) list }

and stmt =
  | Let of { binders : binder list; rhs : comp }
  | DefLvl of name
  | DefFns of { level : var; fns : fn_def list }
  | DefAdts of adt_def list
  | ComptimeMatch of {
      cm_scrut : var;
      cm_matchable : var;
      cm_ctor : int;
      cm_field_names : name list;
    }

and comp =
  | Atom of tyexpr
  | Call of { callee : var; decrease : decrease; cc : cc; args : var list }
  | Match of {
      scrut : var;
      matchable : var;
      ret : match_ret list;
      branches : branch list;
    }
  | Comptime of mult list * expr
  | Inacc
  | ProveSubterm of tyexpr * tyexpr
  | ProvePredates of { subject : var; level : var }
  | PredatesTrans of var * var
  | SubtermTrans of var * var
  | PredatesThroughSubterm of var * var

and binder = { b_name : name; b_mult : mult option; b_sig : entry_sig option }

and match_ret = { mr_mult : mult option; mr_sig : entry_sig }

and branch =
  | Present of name list * expr
  | AbsurdAuto
  | AbsurdProof of name list * expr

and fn_def = {
  fn_name : name;
  params : (name * fn_param) list;
  rets : (name * fn_ret) list;
  body : expr;
}

and adt_def = {
  adt_name : name;
  adt_disc : disc;
  adt_params : (name * entry_sig) list;
  ctors : ctor_def list;
}

and ctor_def = {
  ctor_name : name;
  ctor_mult : mult;
  fields : (name * valctor_field) list;
  ret_args : tyexpr list;
}

type program = expr
