theory wp
imports Main
begin

type_synonym 'id state = "'id \<Rightarrow> int option"

datatype 'id "aexpr" =
    Cst int
  | Var 'id
  | Sub "'id aexpr" "'id aexpr"

datatype 'ty "behaviour" = Enormal 'ty | Eunbound

inductive eval_aexpr :: "'id aexpr \<Rightarrow> 'id state \<Rightarrow> int behaviour \<Rightarrow> bool" where
    eval_cst : "eval_aexpr (Cst n) s (Enormal n)"
  | eval_var : "s x = Some n \<Longrightarrow> eval_aexpr (Var x) s (Enormal n)"
  | eval_var_err : "s x = None \<Longrightarrow> eval_aexpr (Var x) s Eunbound"
  | eval_sub : "eval_aexpr a1 s (Enormal n1) \<Longrightarrow>
                eval_aexpr a2 s (Enormal n2) \<Longrightarrow>
                eval_aexpr (Sub a1 a2) s (Enormal (n1 - n2))"
  | eval_sub_err1 : "eval_aexpr a1 s Eunbound \<Longrightarrow>
                     eval_aexpr (Sub a1 a2) s Eunbound"
  | eval_sub_err2 : "eval_aexpr a2 s Eunbound \<Longrightarrow>
                     eval_aexpr (Sub a1 a2) s Eunbound"

lemmas [intro] = eval_cst eval_var eval_var_err eval_sub eval_sub_err1 eval_sub_err2

(* lemma eval_aexpr_fun : "\<forall>a s b1 b2. eval_aexpr a s b1 \<Longrightarrow>
 *                         eval_aexpr a s b2 \<Longrightarrow> b1 = b2" *)
(* lemma eval_aexpr_fun :
 *   assumes "\<forall>a s b1 b2. eval_aexpr a s b1 \<Longrightarrow>
 *                        eval_aexpr a s b2 \<Longrightarrow> b1 = b2"
 *   proof(induction a)
 *           case (Cst x)
 *   then show ?case using aexpr.distinct(1) aexpr.distinct(3) behaviour.distinct(1) eval_aexpr.cases by blast
 *    next
 *   case (Var x)
 *   then show ?case using eval_aexpr.cases by blast
 *    next
 *   case (Sub a1 a2)
 *   then show ?case using eval_aexpr.cases by blast
 *    qed *)
primrec aeval :: "'id state \<Rightarrow> 'id aexpr \<Rightarrow> int behaviour" ("_\<lbrakk>_\<rbrakk>a" [999,0] 1000) where
  "S\<lbrakk>Cst c\<rbrakk>a = Enormal c"
| "S\<lbrakk>Var x\<rbrakk>a = (case S x of Some n \<Rightarrow> Enormal n | None \<Rightarrow> Eunbound)"
| "S\<lbrakk>Sub a0 a1\<rbrakk>a = (case (S\<lbrakk> a0 \<rbrakk>a , S\<lbrakk> a1 \<rbrakk>a) of
                           (Enormal n0, Enormal n1) \<Rightarrow> Enormal (n0 - n1)
                           | (_,_) \<Rightarrow> Eunbound)"



lemma eval_aexpr_fun : "\<lbrakk> eval_aexpr a s b1; eval_aexpr a s b2 \<rbrakk> \<Longrightarrow> b1 = b2"
    proof(induction a arbitrary: s b1 b2)
          case (Cst x)
       then show ?case by (smt (verit, best) aexpr.distinct(1) aexpr.distinct(3) aexpr.inject(1) eval_aexpr.cases)
        next
       case (Var x)
       then show ?case by (smt (verit) aexpr.distinct(2) aexpr.distinct(6) aexpr.inject(2) eval_aexpr.simps option.discI option.sel)
        next
       case (Sub a1 a2)
       then show ?case by (smt (verit, best) aexpr.distinct(3) aexpr.distinct(5) aexpr.inject(3) behaviour.distinct(1) behaviour.inject eval_aexpr.cases)
        qed


lemma eval_aexpr_total :
  shows "eval_aexpr a S Eunbound \<or> (\<exists> n. eval_aexpr a S (Enormal n))"
  proof(induction a arbitrary: S)
            case (Cst x)
            then show ?case by blast
          next
            case (Var x)
            then show ?case by (metis eval_var eval_var_err option.case_eq_if option.split_sel)
          next
            case (Sub a1 a2)
            then show ?case by (meson eval_sub eval_sub_err1 eval_sub_err2)
          qed

lemma eval_aexpr_equiv: "(S\<lbrakk> a \<rbrakk>a = result) \<Longrightarrow> eval_aexpr a S result"
  proof(induction a arbitrary: S result)
          case (Cst x)
       then show ?case by fastforce
        next
       case (Var x)
       then show ?case by (metis aeval.simps(2) eval_var eval_var_err option.split_sel)
        next
       case (Sub a1 a2)
       then show ?case sorry
        qed



(* lemma eval_aexpr_total "eval_aexpr a s Eunbound \<or> (\<exists> n. eval_aexpr a s (Enormal n))"
 *   proof(induction a) *)
