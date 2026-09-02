type id = int
type mult = Erased | Many
type disc = Enum | Union

type term =
  | Var of id
  | Bound of int
  | App of term * term list
  | Fn of term * tele * tele
  | TyCtor of tele
  | ValCtor of tele * term
  | Matchable of disc * term * (mult * term) list

and tele = entry list
and entry = { name : string option; subterm : bool; mult : mult; sg : sg }
and sg = Ty of term | Is of term

let sg_term = function Ty t | Is t -> t
let map_sg f = function Ty t -> Ty (f t) | Is t -> Is (f t)

let rec map_vars f depth t =
  match t with
  | Var _ | Bound _ -> f depth t
  | App (h, args) -> App (map_vars f depth h, List.map (map_vars f depth) args)
  | Fn (l, ps, rs) ->
      let d, ps = map_tele f depth ps in
      Fn (map_vars f depth l, ps, snd (map_tele f d rs))
  | TyCtor ps -> TyCtor (snd (map_tele f depth ps))
  | ValCtor (ps, r) ->
      let d, ps = map_tele f depth ps in
      ValCtor (ps, map_vars f d r)
  | Matchable (d, t, cs) ->
      Matchable (d, map_vars f depth t, List.map (fun (m, c) -> (m, map_vars f depth c)) cs)

and map_tele f depth es =
  List.fold_left_map (fun d e -> (d + 1, { e with sg = map_sg (map_vars f d) e.sg })) depth es

(* [args] are closed terms, innermost binder first. *)
let instantiate args t =
  let n = List.length args in
  map_vars
    (fun d t ->
      match t with
      | Bound k when k >= d -> if k - d < n then List.nth args (k - d) else Bound (k - n)
      | t -> t)
    0 t

(* [ids] innermost first: the head of the list becomes [Bound 0]. *)
let abstract ids t =
  let index x = let rec go i = function [] -> None | y :: ys -> if x = y then Some i else go (i + 1) ys in go 0 ids in
  map_vars
    (fun d t -> match t with Var x -> (match index x with Some i -> Bound (i + d) | None -> t) | t -> t)
    0 t

let rec fold_vars f acc t =
  match t with
  | Var x -> f acc x
  | Bound _ -> acc
  | App (h, args) -> List.fold_left (fold_vars f) (fold_vars f acc h) args
  | Fn (l, ps, rs) -> fold_tele f (fold_tele f (fold_vars f acc l) ps) rs
  | TyCtor ps -> fold_tele f acc ps
  | ValCtor (ps, r) -> fold_vars f (fold_tele f acc ps) r
  | Matchable (_, t, cs) -> List.fold_left (fun acc (_, c) -> fold_vars f acc c) (fold_vars f acc t) cs

and fold_tele f acc es = List.fold_left (fun acc e -> fold_vars f acc (sg_term e.sg)) acc es

let occurs x t = fold_vars (fun b y -> b || x = y) false t

let rec has_dangling depth t =
  match t with
  | Var _ -> false
  | Bound k -> k >= depth
  | App (h, args) -> has_dangling depth h || List.exists (has_dangling depth) args
  | Fn (l, ps, rs) -> has_dangling depth l || tele_dangling depth ps || tele_dangling (depth + List.length ps) rs
  | TyCtor ps -> tele_dangling depth ps
  | ValCtor (ps, r) -> tele_dangling depth ps || has_dangling (depth + List.length ps) r
  | Matchable (_, t, cs) -> has_dangling depth t || List.exists (fun (_, c) -> has_dangling depth c) cs

and tele_dangling depth es =
  snd (List.fold_left (fun (d, b) e -> (d + 1, b || has_dangling d (sg_term e.sg))) (depth, false) es)

let rec equal a b =
  match (a, b) with
  | Var x, Var y -> x = y
  | Bound i, Bound j -> i = j
  | App (h, xs), App (k, ys) -> equal h k && List.length xs = List.length ys && List.for_all2 equal xs ys
  | Fn (l, ps, rs), Fn (m, qs, ss) -> equal l m && equal_tele ps qs && equal_tele rs ss
  | TyCtor ps, TyCtor qs -> equal_tele ps qs
  | ValCtor (ps, r), ValCtor (qs, s) -> equal_tele ps qs && equal r s
  | Matchable (d, t, cs), Matchable (e, u, ds) ->
      d = e && equal t u && List.length cs = List.length ds
      && List.for_all2 (fun (m, c) (n, d) -> m = n && equal c d) cs ds
  | _ -> false

and equal_tele ps qs =
  List.length ps = List.length qs
  && List.for_all2
       (fun p q ->
         p.subterm = q.subterm && p.mult = q.mult
         && match (p.sg, q.sg) with Ty a, Ty b | Is a, Is b -> equal a b | _ -> false)
       ps qs

let mult_name = function Erased -> "erased" | Many -> "many"
let disc_name = function Enum -> "enum" | Union -> "union"

(* [name_of] resolves free ids; bound names come from the telescopes being printed. *)
let to_string name_of t =
  let rec go bound t =
    match t with
    | Var x -> name_of x
    | Bound k -> (match List.nth_opt bound k with Some (Some n) -> n | _ -> "#" ^ string_of_int k)
    | App (h, args) -> "(" ^ String.concat " " (List.map (go bound) (h :: args)) ^ ")"
    | Fn (l, ps, rs) ->
        let bound, ps = tele bound ps in
        let _, rs = tele bound rs in
        "(Fn " ^ String.concat " " ((go bound l :: ps) @ ("->" :: rs)) ^ ")"
    | TyCtor ps -> "(TyCtor " ^ String.concat " " (snd (tele ~marks:false bound ps) @ [ "->"; "Type" ]) ^ ")"
    | ValCtor (ps, r) ->
        let bound', ps = tele bound ps in
        "(ValCtor " ^ String.concat " " (ps @ [ "->"; go bound' r ]) ^ ")"
    | Matchable (d, t, cs) ->
        "(Matchable " ^ String.concat " "
          (disc_name d :: go bound t :: List.map (fun (m, c) -> "(" ^ mult_name m ^ " " ^ go bound c ^ ")") cs)
        ^ ")"
  and tele ?(marks = true) bound es =
    List.fold_left_map
      (fun bound e ->
        let n = Option.value e.name ~default:"_" in
        let body = match e.sg with Ty t -> go bound t ^ " " ^ n | Is t -> go bound t ^ " is " ^ n in
        let marks = if marks then (if e.subterm then "subterm " else "") ^ mult_name e.mult ^ " " else "" in
        (e.name :: bound, "(" ^ marks ^ body ^ ")"))
      bound es
  in
  go [] t
