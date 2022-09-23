open AltErgoLib

module PA = Parsed_interface
let () = Options.set_is_gui false

open Imp__Constraint

module Var_set = Set.Make (Svar)

(** The variables in a symbolic expression *)
let rec symbolic_expr_vars = function
  | Slit _ ->
    Var_set.empty
  | Svar v ->
    Var_set.singleton v
  | Ssub (e1, e2) ->
    Var_set.union
      (symbolic_expr_vars e1)
      (symbolic_expr_vars e2)

(** The variables in an constraint *)
let rec constraint_vars = function
  | Ctrue | Cfalse ->
    Var_set.empty
  | Ceq (e1, e2) | Cneq (e1, e2) ->
    Var_set.union
      (symbolic_expr_vars e1)
      (symbolic_expr_vars e2)
  | Cconj (c1, c2) ->
    Var_set.union
      (constraint_vars c1)
      (constraint_vars c2)
  | Cexists (v, c) ->
    constraint_vars c

(** The existential variables in an constraint *)
let rec existential_constraint_vars = function
  | Ctrue | Cfalse | Ceq (_, _) | Cneq (_, _) ->
    Var_set.empty
  | Cconj (c1, c2) ->
    Var_set.union
      (existential_constraint_vars c1)
      (existential_constraint_vars c2)
  | Cexists (v, c) ->
    Var_set.add v (existential_constraint_vars c)

let non_existential_constraint_vars c =
  Var_set.diff (constraint_vars c) (existential_constraint_vars c)

(** The Alt-Ergo lexpr for a symbolic expression *)
let rec compile_lexpr = function
  | Slit n ->
    PA.mk_int_const Loc.dummy (Z.to_string n)
  | Svar v ->
    PA.mk_var Loc.dummy (Svar.to_string v)
  | Ssub (e1, e2) ->
    PA.mk_sub Loc.dummy
      (compile_lexpr e1)
      (compile_lexpr e2)

(** The Alt-Ergo lexpr for an constraint *)
let rec compile_constraint = function
  | Ctrue ->
    PA.mk_true_const Loc.dummy
  | Cfalse ->
    PA.mk_false_const Loc.dummy
  | Ceq (e1, e2) ->
    PA.mk_pred_eq Loc.dummy
      (compile_lexpr e1)
      (compile_lexpr e2)
  | Cneq (e1, e2) ->
    PA.mk_pred_not_eq Loc.dummy
      (compile_lexpr e1)
      (compile_lexpr e2)
  | Cconj (c1, c2) ->
    PA.mk_and Loc.dummy
      (compile_constraint c1)
      (compile_constraint c2)
  | Cexists (v, c) ->
    (* let vars = [v, v, PA.int_type] in *)
    (* PA.mk_exists Loc.dummy vars [] [] @@ *)
    compile_constraint c

module SAT = Fun_sat.Make(Theory.Main_Default)
module FE = Frontend.Make(SAT)

let check_sat (c:constr) : bool =
  let goal = (* ∀X.¬C ≍ ∃X.C *)
    let lexpr = compile_constraint c in
    let vars' =
      (* Var_set.diff (constraint_vars c) (existential_constraint_vars c) |> *)
      constraint_vars c |>
      Var_set.elements |>
      List.map Svar.to_string |>
      List.map (fun v -> v, v, PA.int_type)
    in
    PA.mk_goal Loc.dummy "goal" @@
    PA.mk_forall Loc.dummy vars' [] [] @@
    PA.mk_not Loc.dummy @@
    lexpr
  in
  let ltd, _env = Typechecker.file [goal] in
  SAT.reset_refs ();
  Typechecker.split_goals_and_cnf ltd |>
  List.for_all
    (fun p ->
       let sat, consistent, expl =
         let report st n = ()
           (* FE.print_status st n *)
         in
         let aux acc d = FE.process_decl report acc d in
         let acc0 = SAT.empty (), true, Explanation.empty in
         List.fold_left aux acc0 p in
       consistent)

  (* match Typechecker.split_goals ltd with
   *   | [p] ->
   *     SAT.reset_refs ();
   *     let acc0 = SAT.empty (), true, Explanation.empty in
   *     let result = ref None in
   *     let report _d status =
   *       result := Some status
   *       (\* match status with
   *        * | FE.Unsat _ -> result := Some false
   *        * | FE.Inconsistent -> ()
   *        * | FE.Unknown t ->
   *        * | FE.Sat t -> *\)
   *     in
   *     let aux acc d = FE.process_decl report acc d in
   *     ignore @@ List.fold_left aux acc0 p;
   *     true
   *   | _ -> failwith "zero or more than one goals to solve" *)

  (* match Typechecker.split_goals ltd with
   * | [d] ->
   *   let d = Cnf.make (List.map (fun (f, _env) -> f, true) d) in
   *   SAT.reset_refs ();
   *   let stat = ref (Invalid "no answer from Alt-Ergo") in
   *   let f s = stat := s in
   *   begin
   *     try
   *       let _x = Queue.fold (FE.process_decl (report_status f))
   *           (SAT.empty (), true, Explanation.empty) d
   *       in
   *       !stat
   *     with Fun_sat.StepsLimitReached -> Unknown "steps limit reached"
   *   end
   * | _ -> Invalid "zero or more than 1 goal to solve" *)
