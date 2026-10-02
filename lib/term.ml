type id = int
type mult = Erased | Many | Unique
type disc = Enum | Union

type term =
  | Var of id
  | Bound of int
  | App of term * term list
  | Fn of term * tele * tele
  | UniqueFn of term * tele * tele
  | TyCtor of tele
  | ValCtor of tele * term
  | Matchable of disc * bool * bool * term * (mult * term) list
  | SlotHolds of term
  | Cell of term * term list

and tele = entry list
(* [loc] is where the source wrote the entry's binder: a telescope outlives the scope it was read in, so
   carrying it is what lets a message about a binder bound from a stored telescope -- a function's parameter
   inside its own body -- still point at the declaration (ASSUMPTIONS 195). It is not part of the type: a
   telescope compares as if it were absent, which [blank] is where that holds. *)
and entry = { name : string option; subterm : bool; mult : mult; sg : sg; place : term option; loc : Reader.loc }
and sg = Ty of term | Is of term

let sg_term = function Ty t | Is t -> t
let map_sg f = function Ty t -> Ty (f t) | Is t -> Is (f t)

let rec map_vars ?location f depth t =
  match t with
  | Var _ | Bound _ -> f depth t
  | App (h, args) -> App (map_vars ?location f depth h, List.map (map_vars ?location f depth) args)
  | (Fn (l, ps, rs) | UniqueFn (l, ps, rs)) as kind ->
      let d, ps = map_tele ?location f depth ps in
      let l = map_vars ?location f depth l and rs = snd (map_tele ?location f d rs) in
      (match kind with UniqueFn _ -> UniqueFn (l, ps, rs) | _ -> Fn (l, ps, rs))
  | TyCtor ps -> TyCtor (snd (map_tele ?location f depth ps))
  | ValCtor (ps, r) ->
      let d, ps = map_tele ?location f depth ps in
      ValCtor (ps, map_vars ?location f d r)
  | Matchable (d, n, e, t, cs) ->
      Matchable (d, n, e, map_vars ?location f depth t, List.map (fun (m, c) -> (m, map_vars ?location f depth c)) cs)
  | SlotHolds t -> SlotHolds (match location with Some g -> g depth t | None -> map_vars f depth t)
  | Cell (c, ss) -> Cell (map_vars ?location f depth c, List.map (map_vars ?location f depth) ss)

and map_tele ?location f depth es =
  List.fold_left_map (fun d e -> (d + 1, { e with sg = map_sg (map_vars ?location f d) e.sg; place = Option.map (map_vars ?location f d) e.place })) depth es

(* [args] are closed terms, innermost binder first. *)
let subst args d t =
  let n = List.length args in
  match t with Bound k when k >= d -> if k - d < n then List.nth args (k - d) else Bound (k - n) | t -> t

let instantiate args t = map_vars (subst args) 0 t
let instantiate_tele args tele = snd (map_tele (subst args) 0 tele)

let find_index p l = let rec go i = function [] -> None | x :: xs -> if p x then Some i else go (i + 1) xs in go 0 l

(* [ids] innermost first: the head of the list becomes [Bound 0]. *)
let abstract ids t =
  map_vars (fun d t -> match t with Var x -> (match find_index (( = ) x) ids with Some i -> Bound (i + d) | None -> t) | t -> t) 0 t

let tele_parts depth es = List.concat (List.mapi (fun i e -> (depth + i, sg_term e.sg) :: List.map (fun p -> (depth + i, p)) (Option.to_list e.place)) es)

let parts = function
  | Var _ | Bound _ -> []
  | App (h, args) -> List.map (fun t -> (0, t)) (h :: args)
  | Fn (l, ps, rs) | UniqueFn (l, ps, rs) -> ((0, l) :: tele_parts 0 ps) @ tele_parts (List.length ps) rs
  | TyCtor ps -> tele_parts 0 ps
  | ValCtor (ps, r) -> tele_parts 0 ps @ [ (List.length ps, r) ]
  | Matchable (_, _, _, t, cs) -> (0, t) :: List.map (fun (_, c) -> (0, c)) cs
  | SlotHolds t -> [ (0, t) ]
  | Cell (c, ss) -> List.map (fun t -> (0, t)) (c :: ss)

let blank t =
  let hole = Bound 0 in
  let tele = List.map (fun e -> { e with name = None; loc = Reader.nowhere; sg = map_sg (fun _ -> hole) e.sg; place = Option.map (fun _ -> hole) e.place }) in
  match t with
  | Var _ | Bound _ -> t
  | App (_, args) -> App (hole, List.map (fun _ -> hole) args)
  | Fn (_, ps, rs) -> Fn (hole, tele ps, tele rs)
  | UniqueFn (_, ps, rs) -> UniqueFn (hole, tele ps, tele rs)
  | TyCtor ps -> TyCtor (tele ps)
  | ValCtor (ps, _) -> ValCtor (tele ps, hole)
  | Matchable (d, n, e, _, cs) -> Matchable (d, n, e, hole, List.map (fun (m, _) -> (m, hole)) cs)
  | SlotHolds _ -> SlotHolds hole
  | Cell (_, ss) -> Cell (hole, List.map (fun _ -> hole) ss)

let rec fold_vars f depth acc t =
  match t with
  | Var _ | Bound _ -> f depth acc t
  | _ -> List.fold_left (fun acc (k, c) -> fold_vars f (depth + k) acc c) acc (parts t)

let occurs x t = fold_vars (fun _ b t -> b || t = Var x) 0 false t
let has_dangling t = fold_vars (fun d b t -> b || (match t with Bound k -> k >= d | _ -> false)) 0 false t

let rec equal a b = blank a = blank b && List.for_all2 (fun (_, x) (_, y) -> equal x y) (parts a) (parts b)

let mult_name = function Erased -> "erased" | Many -> "many" | Unique -> "unique"
let disc_name = function Enum -> "enum" | Union -> "union"

(* The variable `(SlotVacant)` stands for (UNIQUE.md U10), set once the prelude mints it, so a slot holding it prints
   as the form that wrote it. *)
let vacant = ref (-1)

let univ = ref (-1)
let universe = "(Univ)"

(* [name_of] resolves free ids; bound names come from the telescopes being printed. [kw] spells a keyword. *)
let rec to_string_in ?(kw = Fun.id) name_of bound t =
  let go = to_string_in ~kw name_of in
  let form head items = "(" ^ String.concat " " (kw head :: items) ^ ")" in
  match t with
  | Var x -> name_of x
  | Bound k -> (match List.nth_opt bound k with Some (Some n) -> n | _ -> "#" ^ string_of_int k)
  | App (Var u, []) when u = !univ && kw universe <> universe -> kw universe
  | App (h, args) -> "(" ^ String.concat " " (List.map (go bound) (h :: args)) ^ ")"
  | (Fn (l, ps, rs) | UniqueFn (l, ps, rs)) as kind ->
      let l = go bound l in
      let bound, ps = tele_strings ~kw name_of bound ps in
      let _, rs = tele_strings ~kw name_of bound rs in
      form (match kind with UniqueFn _ -> "UniqueFn" | _ -> "Fn") ((l :: ps) @ (kw "->" :: rs))
  | TyCtor ps -> form "TyCtor" (snd (tele_strings ~kw ~marks:false name_of bound ps) @ [ kw "->"; go bound (App (Var !univ, [])) ])
  | ValCtor (ps, r) ->
      let bound', ps = tele_strings ~kw name_of bound ps in
      form "ValCtor" (ps @ [ kw "->"; go bound' r ])
  | Matchable (d, n, e, t, cs) ->
      form "Matchable"
        ((kw (disc_name d) :: (if n then [ kw "newtype" ] else []) @ (if e then [ kw "extern" ] else []) @ [ go bound t ])
         @ List.map (fun (m, c) -> "(" ^ kw (mult_name m) ^ " " ^ go bound c ^ ")") cs)
  | SlotHolds (Var x) when x = !vacant -> form "SlotVacant" []
  | SlotHolds t -> form "SlotHolds" [ go bound t ]
  | Cell (c, ss) -> form "Cell" (List.map (go bound) (c :: ss))

(* Each entry as the source writes it, `(subterm many (List A) xs at c)`, binding its name for the entries after it. *)
and tele_strings ?(kw = Fun.id) ?(marks = true) name_of bound es =
  List.fold_left_map
    (fun bound e ->
      let go = to_string_in ~kw name_of bound in
      let n = Option.value e.name ~default:"_" in
      let body = match e.sg with Ty t -> go t ^ " " ^ n | Is t -> go t ^ " " ^ kw "is" ^ " " ^ n in
      let marks = if marks then (if e.subterm then kw "subterm" ^ " " else "") ^ kw (mult_name e.mult) ^ " " else "" in
      (e.name :: bound, "(" ^ marks ^ body ^ (match e.place with Some (SlotHolds p) -> " " ^ kw "at" ^ " " ^ go p | None -> "" | _ -> assert false) ^ ")"))
    bound es

let to_string ?kw name_of t = to_string_in ?kw name_of [] t
