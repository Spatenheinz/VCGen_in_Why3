theory bexpr
  imports aexpr
begin

datatype 'b bexpr =
    BCst bool
    | BNot "'b bexpr"
    | BAnd "'b bexpr" "'b bexpr"
    | BLeq "'b aexpr" "'b aexpr"

inductive eval_bexpr :: "int bexpr \<Rightarrow> int state \<Rightarrow> bool behaviour \<Rightarrow> bool" where
EBCst : "eval_bexpr (BCst b) s (Enormal b)"
| EBNot : "eval_bexpr b s (Enormal b') \<Longrightarrow>
           eval_bexpr (BNot b) s (Enormal (\<not> b'))"
| EBNot_err : "eval_bexpr b s Eunbound \<Longrightarrow>
               eval_bexpr (BNot b) s Eunbound"
| EBAnd : "eval_bexpr b1 s (Enormal b1') \<Longrightarrow>
           eval_bexpr b2 s (Enormal b2') \<Longrightarrow>
           b1' \<and> b2' = b3 \<Longrightarrow>
           eval_bexpr (BAnd b1 b2) s (Enormal b3)"
| EBAnd_err1 : "eval_bexpr b1 s Eunbound \<Longrightarrow>
                eval_bexpr (BAnd b1 b2) s Eunbound"
| EBAnd_err2 : "eval_bexpr b1 s (Enormal b1') \<Longrightarrow>
                eval_bexpr b2 s Eunbound \<Longrightarrow>
                eval_bexpr (BAnd b1 b2) s Eunbound"
| EBLeq : "eval_aexpr a1 s (Enormal n1) \<Longrightarrow>
           eval_aexpr a2 s (Enormal n2) \<Longrightarrow>
           eval_bexpr (BLeq a1 a2) s (Enormal (n1 \<le> n2))"
| EBLeq_err1 : "eval_aexpr a1 s Eunbound \<Longrightarrow>
                eval_bexpr (BLeq a1 a2) s Eunbound"
| EBLeq_err2 : "eval_aexpr a1 s (Enormal n1) \<Longrightarrow>
                eval_aexpr a2 s Eunbound \<Longrightarrow>
                eval_bexpr (BLeq a1 a2) s Eunbound"


inductive_cases eval_aexpr_BCstE[elim!]: "eval_aexpr (Cst n) s b"
            and eval_aexpr_BNotE[elim!]: "eval_aexpr (Var n) s b"
            and eval_aexpr_BAndE[elim!]: "eval_aexpr (BinOp a1 op a2) s b"
            and eval_aexpr_BAndE[elim!]: "eval_aexpr (BinOp a1 op a2) s b"



lemma eval_bexpr_fun :
 "\<lbrakk>eval_bexpr b s b1; eval_bexpr b s b2\<rbrakk> \<Longrightarrow> b1 = b2"
proof(induction b arbitrary: b1 s b2)
  case (BCst x)
  then show ?case by(auto intro: eval_bexpr.cases)
next
  case (BNot b)
  then show ?case using eval_bexpr.cases
(*next
  case (BAnd b1 b2)
  then show ?case sorry*)
next
  case (BLeq x1a x2a)
  then show ?case using
    by (smt (verit) behaviour.distinct(1) behaviour.inject bexpr.distinct(5) 
        bexpr.distinct(9) bexpr.inject(4) eval_aexpr_fun_version2 eval_bexpr.cases)
qed

end

