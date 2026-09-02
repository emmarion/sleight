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
  | Newtype of term

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
  | Newtype t -> Newtype (map_vars f depth t)

and map_tele f depth es =
  List.fold_left_map (fun d e -> (d + 1, { e with sg = map_sg (map_vars f d) e.sg })) depth es

(* [args] are closed terms, innermost binder first. *)
let subst args d t =
  let n = List.length args in
  match t with Bound k when k >= d -> if k - d < n then List.nth args (k - d) else Bound (k - n) | t -> t

let instantiate args t = map_vars (subst args) 0 t
let instantiate_tele args tele = snd (map_tele (subst args) 0 tele)

(* [ids] innermost first: the head of the list becomes [Bound 0]. *)
let abstract ids t =
  let index x = let rec go i = function [] -> None | y :: ys -> if x = y then Some i else go (i + 1) ys in go 0 ids in
  map_vars
    (fun d t -> match t with Var x -> (match index x with Some i -> Bound (i + d) | None -> t) | t -> t)
    0 t

let tele_kids depth es = List.mapi (fun i e -> (depth + i, sg_term e.sg)) es

let kids = function
  | Var _ | Bound _ -> []
  | App (h, args) -> List.map (fun t -> (0, t)) (h :: args)
  | Fn (l, ps, rs) -> ((0, l) :: tele_kids 0 ps) @ tele_kids (List.length ps) rs
  | TyCtor ps -> tele_kids 0 ps
  | ValCtor (ps, r) -> tele_kids 0 ps @ [ (List.length ps, r) ]
  | Matchable (_, t, cs) -> (0, t) :: List.map (fun (_, c) -> (0, c)) cs
  | Newtype t -> [ (0, t) ]

let blank t =
  let hole = Bound 0 in
  let tele = List.map (fun e -> { e with name = None; sg = map_sg (fun _ -> hole) e.sg }) in
  match t with
  | Var _ | Bound _ -> t
  | App (_, args) -> App (hole, List.map (fun _ -> hole) args)
  | Fn (_, ps, rs) -> Fn (hole, tele ps, tele rs)
  | TyCtor ps -> TyCtor (tele ps)
  | ValCtor (ps, _) -> ValCtor (tele ps, hole)
  | Matchable (d, _, cs) -> Matchable (d, hole, List.map (fun (m, _) -> (m, hole)) cs)
  | Newtype _ -> Newtype hole

let rec fold_vars f depth acc t =
  match t with
  | Var _ | Bound _ -> f depth acc t
  | _ -> List.fold_left (fun acc (k, c) -> fold_vars f (depth + k) acc c) acc (kids t)

let occurs x t = fold_vars (fun _ b t -> b || t = Var x) 0 false t
let has_dangling depth t = fold_vars (fun d b t -> b || (match t with Bound k -> k >= d | _ -> false)) depth false t

let rec equal a b = blank a = blank b && List.for_all2 (fun (_, x) (_, y) -> equal x y) (kids a) (kids b)

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
    | Newtype t -> "(Newtype " ^ go bound t ^ ")"
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
