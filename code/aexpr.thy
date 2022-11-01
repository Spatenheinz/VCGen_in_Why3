theory aexpr
imports Main
begin

type_synonym 'a state = "'a \<Rightarrow> int option"

datatype aop = Mul | Sub

datatype 'a aexpr =
    Cst int
  | Var 'a
  | BinOp "'a aexpr" aop "'a aexpr"

datatype 'ty behaviour = Enormal 'ty | Eunbound

fun option_from_behaviour :: "'a behaviour \<Rightarrow> 'a option" where
  "option_from_behaviour (Enormal a) = Some a"
| "option_from_behaviour Eunbound = None"

fun behaviour_from_option :: "'a option \<Rightarrow> 'a behaviour" where
  "behaviour_from_option (Some a) = Enormal a"
| "behaviour_from_option None = Eunbound"

lemma prop1 : "behaviour_from_option (option_from_behaviour a) = a"
  by (metis behaviour_from_option.simps(1) behaviour_from_option.simps(2) option_from_behaviour.elims)

lemma prop2 : "option_from_behaviour (behaviour_from_option a) = a"
  by (metis behaviour_from_option.elims option_from_behaviour.simps(1) option_from_behaviour.simps(2))

fun eval_binop :: "aop \<Rightarrow> (int \<Rightarrow> int \<Rightarrow> int)" where
  "eval_binop Mul = (*)"
| "eval_binop Sub = (-)"

inductive eval_aexpr :: "'a aexpr \<Rightarrow> 'a state \<Rightarrow> int behaviour \<Rightarrow> bool" where
    EACst     : "eval_aexpr (Cst n) s (Enormal n)"
  | EAVar     : "s x = Some n \<Longrightarrow>
                 eval_aexpr (Var x) s (Enormal n)"
  | EAVar_err : "s x = None \<Longrightarrow>
                 eval_aexpr (Var x) s Eunbound"
  | EABin     : "eval_aexpr a1 s (Enormal n1) \<Longrightarrow>
                 eval_aexpr a2 s (Enormal n2) \<Longrightarrow>
                 eval_aexpr (BinOp a1 op a2) s (Enormal ((eval_binop op) n1 n2))"
(*  | eval_sub : "eval_aexpr a1 s (Enormal n1) \<Longrightarrow>
                eval_aexpr a2 s (Enormal n2) \<Longrightarrow>
                op = Sub \<Longrightarrow>
                eval_aexpr (BinOp a1 Sub a2) s (Enormal (n1 - n2))" *)
  | EABin_err1 : "eval_aexpr a1 s Eunbound \<Longrightarrow>
                  eval_aexpr (BinOp a1 op a2) s Eunbound"
  | EABin_err2 : "eval_aexpr a1 s (Enormal n) \<Longrightarrow>
                  eval_aexpr a2 s Eunbound \<Longrightarrow>
                  eval_aexpr (BinOp a1 op a2) s Eunbound"

declare eval_aexpr.intros [intro!]

(*lemmas eval_aexpr_induct = eval_aexpr.induct[split_format(complete)] *)

inductive_cases eval_aexpr_CstE[elim!]: "eval_aexpr (Cst n) s b"
            and eval_aexpr_VarE[elim!]: "eval_aexpr (Var n) s b"
            and eval_aexpr_BinOpE[elim!]: "eval_aexpr (BinOp a1 op a2) s b"


lemma eval_aexpr_fun :
  "\<lbrakk>eval_aexpr a s b1; eval_aexpr a s b2\<rbrakk> \<Longrightarrow> b1 = b2"
  by (induction arbitrary: b2 rule: eval_aexpr.induct) auto


code_pred (modes: i => i => o => bool as bigstepA) eval_aexpr .
definition "bigstep_ex1 a s = Predicate.the (bigstepA a s)"
value "bigstep_ex1 (Var 1) (\<lambda>x. (if x = 4 then Some 10 else None))"


(*code_pred (modes: i => i \<Rightarrow> o => bool as bigstep') eval_aexpr2 .
definition "bigstep_ex t = Predicate.the (bigstep' t)"
*)

primrec aeval :: "'a state \<Rightarrow> 'a aexpr \<Rightarrow> int behaviour" ("_\<lbrakk>_\<rbrakk>a" [999,0] 1000) where
  "S\<lbrakk>Cst c\<rbrakk>a = Enormal c"
| "S\<lbrakk>Var x\<rbrakk>a = (case S x of Some n \<Rightarrow> Enormal n | None \<Rightarrow> Eunbound)"
| "S\<lbrakk>BinOp a0 op a1\<rbrakk>a = (case (S\<lbrakk> a0 \<rbrakk>a , S\<lbrakk> a1 \<rbrakk>a) of
                           (Enormal n0, Enormal n1) \<Rightarrow> Enormal ((eval_binop op) n0 n1)
                           | (_,_) \<Rightarrow> Eunbound)"

export_code bigstep_ex1 Cst Mul in OCaml file_prefix "core"
export_code aeval Cst Mul in OCaml file_prefix "aeval"

(* following tries to prove without bottom *)
type_synonym 'a state2 = "'a \<Rightarrow> int"

inductive eval_aexpr2 :: "int aexpr \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> bool" where
    eval_cst : "eval_aexpr2 (Cst n) s n"
  | eval_var : "eval_aexpr2 (Var x) s (s x)"
  | eval_mul : "eval_aexpr2 a1 s n1 \<Longrightarrow>
                eval_aexpr2 a2 s n2 \<Longrightarrow>
                op = Mul \<Longrightarrow>
                eval_aexpr2 (BinOp a1 op a2) s(n1 * n2)"
  | eval_sub : "eval_aexpr2 a1 s n1 \<Longrightarrow>
                eval_aexpr2 a2 s n2 \<Longrightarrow>
                op = Sub \<Longrightarrow>
                eval_aexpr2 (BinOp a1 Sub a2) s (n1 - n2)"

code_pred (modes: i => i => o => bool as bigstep') eval_aexpr2 .
definition "bigstep_ex t s = Predicate.the (bigstep' t s)"
(*value "bigstep_ex (Var 6) (\<lambda>x. (if x = 4 then 5 else undefined))" *)
(*lemma eval_aexpr_fun2 :
  "\<lbrakk>eval_aexpr2 a s b1; eval_aexpr2 a s b2\<rbrakk> \<Longrightarrow> b1 = b2"
proof(induction a s b1 arbitrary: b2 rule: eval_aexpr2.induct)
  case (eval_cst n s)
  then show ?case
    by (metis aexpr.distinct(1) aexpr.distinct(4) aexpr.inject(1) eval_aexpr2.simps)
next
  case (eval_var x s n)
  then show ?case
    by (metis aexpr.distinct(2) aexpr.inject(2) aexpr.simps(9) eval_aexpr2.simps)
next
  case (eval_mul a1 s n1 a2 n2 op)
  then show ?case
    by (smt (verit) aexpr.distinct(3) aexpr.distinct(5) aexpr.inject(3) aop.distinct(1) eval_aexpr2.simps)
next
  case (eval_sub a1 s n1 a2 n2 op)
  then show ?case
    by (smt (verit) aexpr.distinct(3) aexpr.distinct(5) aexpr.inject(3) aop.distinct(1) eval_aexpr2.simps)
qed *)
lemma eval_aexpr_fun22 :
  "\<lbrakk>eval_aexpr2 a s b1; eval_aexpr2 a s b2\<rbrakk> \<Longrightarrow> b1 = b2"
proof(induction a arbitrary: b1 b2)
  case (Cst x)
  then show ?case by (auto intro: eval_aexpr2.cases)
    (* by (smt (verit, ccfv_SIG) aexpr.distinct(1) aexpr.distinct(3) aexpr.inject(1) eval_aexpr2.simps) *)
next
  case (Var x)
  then show ?case by (auto intro: eval_aexpr2.cases)
    (*by (metis aexpr.distinct(2) aexpr.inject(2) aexpr.simps(9) eval_aexpr2.simps) *)
next
  case (BinOp a1 x2a a2)
  then show ?case
    by (smt (verit, ccfv_SIG) aexpr.distinct(3) aexpr.distinct(5)
        aexpr.inject(3) aop.distinct(1) eval_aexpr2.simps)
qed
 
(* no bottom ends here *)


lemma eval_aexpr_total :
  shows "eval_aexpr a S Eunbound \<or> (\<exists> n. eval_aexpr a S (Enormal n))"
proof(induction a arbitrary: S)
  case (Cst x)
  then show ?case by blast
next
  case (Var x)
  then show ?case
    by (meson EAVar EAVar_err not_Some_eq)
next
  case (BinOp a1 x2a a2)
  then show ?case
    by (meson EABin EABin_err1 EABin_err2)
qed

lemma eval_aexpr_equiv: "(S\<lbrakk> a \<rbrakk>a = result) \<Longrightarrow> eval_aexpr a S result"
proof(induction a arbitrary: result)
  case (Cst x)
       then show ?case by fastforce
        next
  case (Var x)
       then show ?case
         by (metis aeval.simps(2) EAVar EAVar_err option.split_sel)
  next
  case (BinOp a1 op a2)
  then show ?case sorry
 qed


end
