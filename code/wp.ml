let rec mem (x: Z.t) (l: (Z.t) list) : bool =
  match l with
  | [] -> false
  | y :: r -> Z.equal x y || mem x r

let rec assigned_vars (s: (Z.t) stmt) (vars: (Z.t) list) : (Z.t) list =
  match s with
  | Sskip -> vars
  | Sseq (s1, s2) -> assigned_vars s2 (assigned_vars s1 vars)
  | Sass (x, _) -> x :: vars
  | Sassert _ -> vars
  | Sif (_, s1, s2) -> assigned_vars s2 (assigned_vars s1 vars)
  | Swhile (_, _, s1) -> assigned_vars s1 vars

let rec abstract_all_vars (vars: (Z.t) list) (seen: (Z.t) list)
                          (f: (Z.t) formula) : (Z.t) formula =
  match vars with
  | [] -> f
  | x :: xs ->
    if mem x seen
    then abstract_all_vars xs seen f
    else
      begin
        let v = fresh_from f in let f' = subst_fmla f x v in
        abstract_all_vars xs (x :: seen) (Fall (v, f')) end

let abstract_effects (s: (Z.t) stmt) (f: (Z.t) formula) : (Z.t) formula =
  let vars = assigned_vars s ([] ) in abstract_all_vars vars ([] ) f

let rec wp (s: (Z.t) stmt) (q: (Z.t) formula) : (Z.t) formula =
  match s with
  | Sskip -> q
  | Sseq (s1, s2) -> wp s1 (wp s2 q)
  | Sassert p -> Fand (p, Fimp (p, q))
  | Sass (x,
    e) ->
    (let y = fresh_from q in
     Fall (y,
     Fimp (Fand (Fterm (Bleq (Avar y, e)), Fterm (Bleq (e, Avar y))),
     subst_fmla q x y)))
  | Sif (b,
    s1,
    s2) ->
    Fand (Fimp (Fterm b, wp s1 q), Fimp (Fnot (Fterm b), wp s2 q))
  | Swhile (cond,
    inv,
    body) ->
    Fand (inv,
    abstract_effects body
    (Fand (Fimp (Fand (Fterm cond, inv), wp body inv),
     Fimp (Fand (Fnot (Fterm cond), inv), q))))

