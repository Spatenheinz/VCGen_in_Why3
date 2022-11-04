type state = {
  mutable lst: ((Z.t) * (Z.t)) list;
  }

let empty (_: unit) : state = { lst = []  }

let sigma = empty ()

type aop =
  | Mul
  | Sub
  | Add

type 'a aexpr =
  | Acst of (Z.t)
  | Avar of 'a
  | ABin of ('a aexpr) * aop * ('a aexpr)

exception Unbound

let rec find (k: Z.t) (s: state) : Z.t =
  match s.lst with
  | (k', n) :: s' ->
    if Z.leq k k' && Z.leq k' k then n else find k { lst = s' }
  | [] -> raise Unbound

let eval_op (op: aop) : Z.t -> Z.t -> Z.t =
  match op with
  | Mul -> Z.mul 
  | Sub -> Z.sub 
  | Add -> Z.add 

let rec aeval (a: (Z.t) aexpr) : Z.t =
  match a with
  | Acst i -> i
  | Avar v -> find v sigma
  | ABin (a1,
    op,
    a2) ->
    (let o = aeval a2 in let o1 = let o2 = aeval a1 in eval_op op o2 in o1 o)

type 'a bexpr =
  | BCst of (bool)
  | Bleq of ('a aexpr) * ('a aexpr)
  | Band of ('a bexpr) * ('a bexpr)
  | Bnot of ('a bexpr)

let rec beval (b: (Z.t) bexpr) : bool =
  match b with
  | BCst b1 -> b1
  | Bleq (a1, a2) -> (let o = aeval a2 in let o1 = aeval a1 in Z.leq o1 o)
  | Band (b1, b2) -> (let o = beval b2 in let o1 = beval b1 in o1 && o)
  | Bnot b1 -> not (beval b1)

type 'a formula =
  | Fterm of ('a bexpr)
  | Fand of ('a formula) * ('a formula)
  | Fnot of ('a formula)
  | Fimp of ('a formula) * ('a formula)
  | Fall of 'a * ('a formula)

type 'a stmt =
  | Sskip
  | Sass of 'a * ('a aexpr)
  | Sseq of ('a stmt) * ('a stmt)
  | Sassert of ('a formula)
  | Sif of ('a bexpr) * ('a stmt) * ('a stmt)
  | Swhile of ('a bexpr) * ('a formula) * ('a stmt)

let add (k: Z.t) (v: Z.t) (s: state) : unit = s.lst <- (k, v) :: s.lst

let rec seval (s: (Z.t) stmt) : unit =
  match s with
  | (Sskip | Sassert _) -> ()
  | Sass (x, a) -> (let o = aeval a in add x o sigma)
  | Sseq (s1, s2) -> seval s1; seval s2
  | Sif (b, s1, s2) -> if beval b then seval s1 else seval s2
  | Swhile (e, _, body) -> while beval e do
                             seval body done

let state_lst (s: state) : ((Z.t) * (Z.t)) list = s.lst

let clear (s: state) : unit = s.lst <- [] 

let eval_prog (s: (Z.t) stmt) : ((Z.t) * (Z.t)) list =
  seval s; let res = state_lst sigma in clear sigma; res

let test (_: unit) : unit = seval (Sass (Z.one, Acst (Z.of_string "5")))

