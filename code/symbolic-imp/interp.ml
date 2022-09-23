open Format

module Imp = struct
  module Syntax = Imp__Syntax
  module Constraint = Imp__Constraint
  module Interp = Imp__ConcreteInterpreter
  module SymInterp = Imp__SymbolicInterpreter
  module SymState = Imp__SymState
  module Svar = Svar
  module SymStateSet = SymStateSet
end

open Imp
open Imp.Syntax

let rec print_expr fmt e =
  match e with
  | Elit n -> fprintf fmt "%s" (Z.to_string n)
  | Evar v -> fprintf fmt "%s" v
  | Esub(e1,e2) -> fprintf fmt "@[%a -@ %a@]" print_expr e1 print_expr e2

let rec print_statement fmt s =
  match s with
  | Cskip -> fprintf fmt "skip"
  | Cassign(v,e) -> fprintf fmt "@[%s :=@ %a@]" v print_expr e
  | Cseq(s1,s2) -> fprintf fmt "@[%a ;@\n%a@]" print_statement s1 print_statement s2
  | Cif(e,s1,s2) ->
     fprintf fmt "@[if %a@ then %a@ else %a@]" print_expr e print_statement s1 print_statement s2
  | Cwhile(e,s1) ->
     fprintf fmt "@[while %a@ do %a@ done@]" print_expr e print_statement s1

let print_program fmt p =
  fprintf fmt "@[<v 0>begin@ %a@ end@]" print_statement p

let print_env fmt e =
  Hashtbl.iter
    (fun k v -> fprintf fmt "%s -> %s@\n" k (Z.to_string v))
    e

let print_symbolic_env fmt e =
  let pp_sep fmt () = fprintf fmt ",@ " in
  fprintf fmt "@[";
  Constraint.PVMap.bindings e |>
  pp_print_list ~pp_sep (fun fmt (x, v) -> fprintf fmt "%s → %s" x (Svar.to_string v)) fmt;
  fprintf fmt "@]"

let rec print_expr fmt e =
  let open Constraint in
  match e with
  | Slit n -> fprintf fmt "%s" (Z.to_string n)
  | Svar v -> fprintf fmt "%s" (Svar.to_string v)
  | Ssub(e1,e2) -> fprintf fmt "@[%a -@ %a@]" print_expr e1 print_expr e2

let rec print_constraint fmt c =
  let open Constraint in
  match c with
  | Ctrue -> fprintf fmt "True"
  | Cfalse -> fprintf fmt "False"
  | Ceq(e1,e2) -> fprintf fmt "@[%a =@ %a@]" print_expr e1 print_expr e2
  | Cneq(e1,e2) -> fprintf fmt "@[%a ≠@ %a@]" print_expr e1 print_expr e2
  | Cconj(c1,c2) -> fprintf fmt "@[%a ∧@ %a@]" print_constraint c1 print_constraint c2
  | Cexists(v, c1) -> fprintf fmt "@[∃ %s.@ %a@]" (Svar.to_string v) print_constraint c1

let print_state fmt s =
  fprintf fmt "@[<v 1>(%a |@ %a)@]"
          print_symbolic_env s.SymState.sigma
          print_constraint s.SymState.constr

let print_state_set fmt s =
  let _i =
    SymStateSet.fold
      (fun st i ->
       fprintf fmt "@\n@[state %d: %a@]" i print_state st; i+1)
      s 0
  in ()

let print_states fmt (s1,s2,s3) =
  printf "@[<v 2>Normal states: %d%a@]@\n"
         (SymStateSet.cardinal s1)
         print_state_set s1;
  printf "@[<v 2>Unbound variables: %d%a@]@\n"
         (SymStateSet.cardinal s2)
         print_state_set s2;
  printf "@[<v 2>Loop limits: %d%a@]"
         (SymStateSet.cardinal s3)
         print_state_set s3



let empty_env = Constraint.PVMap.empty

let empty_state = SymState.{
      sigma = empty_env;
      constr = Constraint.Ctrue;
    }

let x_var = Svar.fresh ()

let x_env = Constraint.PVMap.add
              "x" x_var empty_env

let x_state = SymState.{
    sigma= x_env;
    constr = Constraint.Ctrue;
  }

let x_state_non_zero = SymState.{
    sigma= x_env;
    constr = Constraint.(Cneq (Svar x_var, Slit (Z.of_int 0)));
  }

let assign v e = Cassign (v, e)
let lit n = Elit (Z.of_int n)
let var x = Evar x
let seq = function
  | [] -> failwith "seq"
  | c::cs -> List.fold_left (fun c1 c2 -> Cseq (c1, c2)) c cs
let fail = Cwhile (Elit (Z.of_int 1), Cskip) (* Cassign("xxx", Evar "xxx") *)
let skip = Cskip
let while_ e c = Cwhile (e, c)
let if_ e c1 c2 = Cif (e, c1, c2)
let sub e1 e2 = Esub (e1, e2)

let p1 = assign "x" @@ lit 50
let p2 = assign "y" @@ sub (var "x") (lit 8)
let p2' = assign "x" @@ sub (var "x") (lit 8)
let p3 = seq [p1;p2]
let p4 = if_ (sub (var "x") (lit 0)) p1 p2

let p4' =
  if_ (var "x")
    (if_ (sub (var "x") (lit 1)) fail Cskip)
    skip

let p4'' =
  seq [
    assign "y" @@ var "x";
    assign "x" @@ sub (var "x") (lit 1);
    if_ (sub (var "y") (var "x")) Cskip fail
  ]

let p5 = while_ (var "x") (assign "x" (sub (var "x") (lit 1)))

let p6 = while_ (var "x") skip

let p7 =
  seq [
    assign "y" @@ var "x";
    assign "x" @@ sub (var "x") @@ sub (var "x") (var "x");
    if_ (var "x") skip fail
  ]

let () =
  printf "=== Concrete execution ===@.";
  let open Interp in
  Hashtbl.clear env;
  interp_cmd p3;
  printf "%a@." print_env env;
  printf "@\n@."

let cnf =
  Z.of_int
    (try int_of_string (Unix.getenv "LOOP_BOUNDARY")
     with _ -> 8)

let exec p s =
  let r = SymInterp.symbolic_interp_cmd cnf s p in
  printf "@[<v 2>Executing@\n%a@\nInitial state %a@\n%a@]@\n@."
         print_program p print_state s print_states r

let () =
  printf "=== Symbolic execution ===@.";
  (* exec p2 empty_state; *)
  exec p2 x_state;
  exec p2' x_state;
  exec p3 empty_state;
  exec p4 x_state;
  exec p4'' x_state;
  (* exec p4' x_state; *)
  exec p5 x_state;
  exec p6 x_state;
  exec p7 x_state;
  exec p7 x_state_non_zero;
  printf "@\n@."
