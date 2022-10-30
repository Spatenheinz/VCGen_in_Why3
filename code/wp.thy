theory wp
imports Main
begin

type_synonym state = "string \<Rightarrow> int option"

datatype "aexpr" =
    Cst int
  | Var string
  | Sub aexpr aexpr
  | Mul aexpr aexpr 

datatype 'ty "behaviour" = Enormal 'ty | Eunbound

inductive eval_aexpr :: "aexpr \<Rightarrow> state \<Rightarrow> int behaviour \<Rightarrow> bool" where
    eval_cst : "eval_aexpr (Cst n) s (Enormal n)"
  | eval_var : "s x = Some n \<Longrightarrow> eval_aexpr (Var x) s (Enormal n)"
  | eval_var_err : "s x = None \<Longrightarrow> eval_aexpr (Var x) s Eunbound"
  | eval_sub : "eval_aexpr a1 s (Enormal n1) \<Longrightarrow>
                eval_aexpr a2 s (Enormal n2) \<Longrightarrow>
                eval_aexpr (Sub a1 a2) s (Enormal (n1 - n2))"
  | eval_sub_err1 : "eval_aexpr a1 s Eunbound \<Longrightarrow>
                     eval_aexpr (Sub a1 a2) s Eunbound"
  | eval_sub_err2 : "eval_aexpr a1 s (Enormal n) \<Longrightarrow>
                     eval_aexpr a2 s Eunbound \<Longrightarrow>
                     eval_aexpr (Sub a1 a2) s Eunbound"
  | eval_mul : "eval_aexpr a1 s (Enormal n1) \<Longrightarrow>
                eval_aexpr a2 s (Enormal n2) \<Longrightarrow>
                eval_aexpr (Mul a1 a2) s (Enormal (n1 * n2))"
  | eval_mul_err1 : "eval_aexpr a1 s Eunbound \<Longrightarrow>
                     eval_aexpr (Mul a1 a2) s Eunbound"
  | eval_mul_err2 : "eval_aexpr a1 s (Enormal n) \<Longrightarrow>
                     eval_aexpr a2 s Eunbound \<Longrightarrow>
                     eval_aexpr (Mul a1 a2) s Eunbound"

code_pred eval_aexpr .

lemmas [intro] = eval_cst eval_var eval_var_err eval_sub eval_sub_err1 eval_sub_err2 eval_mul eval_mul_err1 eval_mul_err2

primrec aeval :: "state \<Rightarrow> aexpr \<Rightarrow> int behaviour" ("_\<lbrakk>_\<rbrakk>a" [999,0] 1000) where
  "S\<lbrakk>Cst c\<rbrakk>a = Enormal c"
| "S\<lbrakk>Var x\<rbrakk>a = (case S x of Some n \<Rightarrow> Enormal n | None \<Rightarrow> Eunbound)"
| "S\<lbrakk>Sub a0 a1\<rbrakk>a = (case (S\<lbrakk> a0 \<rbrakk>a , S\<lbrakk> a1 \<rbrakk>a) of
                           (Enormal n0, Enormal n1) \<Rightarrow> Enormal (n0 - n1)
                           | (_,_) \<Rightarrow> Eunbound)"
| "S\<lbrakk>Mul a0 a1\<rbrakk>a = (case (S\<lbrakk> a0 \<rbrakk>a , S\<lbrakk> a1 \<rbrakk>a) of
                           (Enormal n0, Enormal n1) \<Rightarrow> Enormal (n0 * n1)
                           | (_,_) \<Rightarrow> Eunbound)"


lemma eval_aexpr_fun : 
  "\<lbrakk>eval_aexpr a s b1; eval_aexpr a s b2\<rbrakk> \<Longrightarrow> b1 = b2"
  by (metis Abs_unit_inverse Collect_cong Rep_unit UNIV_def bot_unit_def default_unit_def elem_set
     eval_single mem_Collect_eq old.unit.exhaust option.inject option.simps(15) singleI_unit sup_bot.monoid_axioms)

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
          next
            case (Mul a1 a2)
            then show ?case by (meson eval_mul eval_mul_err1 eval_mul_err2)
          qed
          
lemma eval_aexpr_equiv: "(S\<lbrakk> a \<rbrakk>a = result) \<Longrightarrow> eval_aexpr a S result"
proof(induction a arbitrary: result)
          case (Cst x)
       then show ?case by fastforce
        next
       case (Var x)
       then show ?case by (metis aeval.simps(2) eval_var eval_var_err option.split_sel)
        next
       case (Sub a1 a2)
       then show ?case
         apply(simp)
         by (smt (verit, del_insts) behaviour.simps(4) behaviour.simps(5)
             eval_aexpr_fun eval_aexpr_total eval_sub eval_sub_err1 eval_sub_err2)
        next
        case (Mul a1 a2)
        then show ?case
         apply(simp)
         by (smt (verit, del_insts) behaviour.simps(4) behaviour.simps(5)
             eval_aexpr_fun eval_aexpr_total eval_mul eval_mul_err1 eval_mul_err2)
        qed
