theory bexpr
  imports aexpr
begin

datatype 'b bexpr =
    BCst bool
    | BNot "'b bexpr"
    | BAnd "'b bexpr" "'b bexpr"
    | BLeq "'b aexpr" "'b aexpr"

inductive eval_bexpr :: " 'a bexpr \<Rightarrow> 'a state \<Rightarrow> bool behaviour \<Rightarrow> bool" where
EBCst : "eval_bexpr (BCst b) s (Enormal b)"
| EBNot : "eval_bexpr b s (Enormal b') \<Longrightarrow>
           eval_bexpr (BNot b) s (Enormal (\<not> b'))"
| EBNot_err : "eval_bexpr b s Eunbound \<Longrightarrow>
               eval_bexpr (BNot b) s Eunbound"
| EBAnd : "eval_bexpr b1 s (Enormal b1') \<Longrightarrow>
           eval_bexpr b2 s (Enormal b2') \<Longrightarrow>
           eval_bexpr (BAnd b1 b2) s (Enormal (b1' \<and> b2'))"
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

inductive_cases eval_bexpr_BCstE[elim!]: "eval_bexpr (BCst n) s b"
            and eval_bexpr_BNotE[elim!]: "eval_bexpr (BNot b1) s b"
            and eval_bexpr_BAndE[elim!]: "eval_bexpr (BAnd b1 b2) s b"
            and eval_bexpr_BLeqE[elim!]: "eval_bexpr (BLeq a1 a2) s b"

thm eval_bexpr_BLeqE

lemma eval_bexpr_fun :
 "\<lbrakk>eval_bexpr b s b1; eval_bexpr b s b2\<rbrakk> \<Longrightarrow> b1 = b2"
proof(induction arbitrary: b2 rule: eval_bexpr.induct)
  case (EBLeq a1 s n1 a2 n2)
  then show ?case 
    using eval_bexpr_BLeqE eval_aexpr_fun
    by (metis behaviour.inject behaviour.simps(3))
next
  case (EBLeq_err1 a1 s a2)
  then show ?case 
    using eval_aexpr_fun by blast
next
  case (EBLeq_err2 a1 s n1 a2)
  then show ?case
    using eval_aexpr_fun by blast
next
qed auto

end

