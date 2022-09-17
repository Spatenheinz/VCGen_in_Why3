type id = Z.t

type state = id -> Z.t

type aexpr =
  | Acst of (Z.t)
  | Asub of aexpr * aexpr

type bexpr =
  | Btrue
  | Bfalse
  | Bleq of aexpr * aexpr

type stmt =
  | Sskip
  | Sass of id * aexpr
  | Sseq of stmt * stmt

type prog = stmt

let pone (i: Z.t) : Z.t = Z.add i Z.one

let rec aeval (e: aexpr) (st: id -> Z.t) : Z.t =
  match e with
  | Acst i -> i
  | Asub (e1, e2) -> Z.sub (aeval e1 st) (aeval e2 st)

