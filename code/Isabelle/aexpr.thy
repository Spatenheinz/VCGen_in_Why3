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
  | EABin_err1 : "eval_aexpr a1 s Eunbound \<Longrightarrow>
                  eval_aexpr (BinOp a1 op a2) s Eunbound"
  | EABin_err2 : "eval_aexpr a1 s (Enormal n) \<Longrightarrow>
                  eval_aexpr a2 s Eunbound \<Longrightarrow>
                  eval_aexpr (BinOp a1 op a2) s Eunbound"

declare eval_aexpr.intros [intro!]

inductive_cases eval_aexpr_CstE[elim!]: "eval_aexpr (Cst n) s b"
            and eval_aexpr_VarE[elim!]: "eval_aexpr (Var n) s b"
            and eval_aexpr_BinOpE[elim!]: "eval_aexpr (BinOp a1 op a2) s b"


lemma eval_aexpr_fun :
  "\<lbrakk>eval_aexpr a s b1; eval_aexpr a s b2\<rbrakk> \<Longrightarrow> b1 = b2"
  by (induction arbitrary: b2 rule: eval_aexpr.induct) auto


code_pred (modes: i => i => o => bool as bigstepA) eval_aexpr .
definition "bigstep_ex1 a s = Predicate.the (bigstepA a s)"


export_code bigstep_ex1 Cst Mul in OCaml file_prefix "core"


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

end
