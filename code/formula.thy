theory formula
  imports bexpr
begin

datatype 'a formula =
  FTerm "'a bexpr"
  | FAnd "'a formula" "'a formula"
  | FNot "'a formula"
  | FImp "'a formula" "'a formula"
  | FAll "'a" "'a formula"

fun fresh_in_aexpr :: "int \<Rightarrow> int aexpr \<Rightarrow> bool" where
  "fresh_in_aexpr _ (Cst _) \<longleftrightarrow> True" |
  "fresh_in_aexpr ident (Var v) \<longleftrightarrow> (ident \<noteq> v)" |
  "fresh_in_aexpr ident (BinOp a1 _ a2) \<longleftrightarrow> fresh_in_aexpr ident a1 \<and> fresh_in_aexpr ident a2"

fun fresh_in_bexpr :: "int \<Rightarrow> int bexpr \<Rightarrow> bool" where
  "fresh_in_bexpr _ (BCst _) \<longleftrightarrow> True" |
  "fresh_in_bexpr ident (BNot b) \<longleftrightarrow> fresh_in_bexpr ident b" |
  "fresh_in_bexpr ident (BAnd b1 b2) \<longleftrightarrow> 
                  fresh_in_bexpr ident b1 \<and> fresh_in_bexpr ident b2" |
  "fresh_in_bexpr ident (BLeq a1 a2) \<longleftrightarrow> 
                  fresh_in_aexpr ident a1 \<and> fresh_in_aexpr ident a2"

fun fresh_in_formula :: "int \<Rightarrow> int formula \<Rightarrow> bool" where
  "fresh_in_formula ident (FTerm b) \<longleftrightarrow> fresh_in_bexpr ident b"
| "fresh_in_formula ident (FNot f) \<longleftrightarrow> fresh_in_formula ident f"
| "fresh_in_formula ident (FAnd f1 f2) \<longleftrightarrow> fresh_in_formula ident f1 \<and> fresh_in_formula ident f2"
| "fresh_in_formula ident (FImp f1 f2) \<longleftrightarrow> fresh_in_formula ident f1 \<and> fresh_in_formula ident f2"
| "fresh_in_formula ident (FAll v f)  \<longleftrightarrow> ident \<noteq> v \<and> fresh_in_formula ident f"

fun max_id_aexpr :: "int \<Rightarrow> int aexpr \<Rightarrow> int" where
  "max_id_aexpr ident (Cst _) = ident" |
  "max_id_aexpr ident (Var v) =  max ident v" |
  "max_id_aexpr ident (BinOp a1 _ a2) = max (max_id_aexpr ident a1) (max_id_aexpr ident a2)"

fun max_id_bexpr :: "int \<Rightarrow> int bexpr \<Rightarrow> int" where
  "max_id_bexpr ident (BCst _) = ident" |
  "max_id_bexpr ident (BNot b) =  max_id_bexpr ident b" |
  "max_id_bexpr ident (BAnd b1 b2) = max (max_id_bexpr ident b1) (max_id_bexpr ident b2)" |
  "max_id_bexpr ident (BLeq a1 a2) = max (max_id_aexpr ident a1) (max_id_aexpr ident a2)"

fun max_id_formula :: "int \<Rightarrow> int formula \<Rightarrow> int" where
  "max_id_formula ident (FTerm b) = max_id_bexpr ident b"
| "max_id_formula ident (FNot f) = max_id_formula ident f"
| "max_id_formula ident (FAnd f1 f2) = max (max_id_formula ident f1) (max_id_formula ident f2)"
| "max_id_formula ident (FImp f1 f2) = max (max_id_formula ident f1) (max_id_formula ident f2)"
| "max_id_formula ident (FAll v f) = max v (max_id_formula ident f)"

fun fv_aexpr :: "'a aexpr \<Rightarrow> 'a set" where
  "fv_aexpr (Cst _) = {}"
| "fv_aexpr (Var v) = {v}"
| "fv_aexpr (BinOp a1 _ a2) = fv_aexpr a1 \<union> fv_aexpr a2"

fun fv_bexpr :: "'a bexpr \<Rightarrow> 'a set" where
  "fv_bexpr (BCst _) = {}"
| "fv_bexpr (BAnd b1 b2) = fv_bexpr b1 \<union> fv_bexpr b2"
| "fv_bexpr (BLeq a1 a2) = fv_aexpr a1 \<union> fv_aexpr a2"
| "fv_bexpr (BNot b) = fv_bexpr b"

fun fv_formula :: "'a formula \<Rightarrow> 'a set" where
  "fv_formula (FTerm b) = fv_bexpr b"
| "fv_formula (FNot f) = fv_formula f"
| "fv_formula (FAnd f1 f2) = fv_formula f1 \<union> fv_formula f2"
| "fv_formula (FImp f1 f2) = fv_formula f1 \<union> fv_formula f2"
| "fv_formula (FAll v f) = fv_formula f - {v}"

fun bv_formula :: "'a formula \<Rightarrow> 'a set" where
  "bv_formula (FTerm b) = {}"
| "bv_formula (FNot f) = bv_formula f"
| "bv_formula (FAnd f1 f2) = bv_formula f1 \<union> bv_formula f2"
| "bv_formula (FImp f1 f2) = bv_formula f1 \<union> bv_formula f2"
| "bv_formula (FAll v f) = {v} \<union> bv_formula f"

definition vars_in_formula :: "'a formula \<Rightarrow> 'a set" where
  "vars_in_formula f = fv_formula f \<union> bv_formula f"


definition fresh_from :: "int formula \<Rightarrow> int" where
  "fresh_from f = max_id_formula 0 f + 1"

lemma max_id_trivial : "max_id_aexpr 0 a \<ge> 0"
  by(induction a) simp_all

lemma max_id_geq: "v = max_id_aexpr 0 a \<Longrightarrow> (\<forall>x \<in> (fv_aexpr a). v \<ge> x)"
  by(induction a arbitrary: v)(auto)

lemma id_suc_not_vars : "v = max_id_aexpr 0 a \<Longrightarrow> (v + 1) \<notin> (fv_aexpr a)"
proof(induction a arbitrary: v)
  case (BinOp a1 op a2)
  have "v = max_id_aexpr 0 (BinOp a1 op a2)"
    using BinOp.prems by blast
  hence "\<forall> x \<in> (fv_aexpr (BinOp a1 op a2)). v \<ge> x"
    using max_id_geq
    by blast
  then show ?case
    by fastforce
qed auto

lemma id_fresh_iff : "v \<notin> fv_aexpr a \<Longrightarrow> fresh_in_aexpr v a"
  by(induction a arbitrary: v) auto

lemma max_plus_fresh : "v = max_id_aexpr 0 a \<Longrightarrow> fresh_in_aexpr (v + 1) a"
proof(induction a arbitrary: v)
  case (BinOp a1 op a2)
  have "(v + 1) \<notin> fv_aexpr (BinOp a1 op a2)"
    using BinOp.prems id_suc_not_vars by blast
  then show ?case
    using id_fresh_iff by auto
qed auto

lemma id_fresh_iff_b : "v \<notin> fv_bexpr b \<Longrightarrow> fresh_in_bexpr v b"
  by(induction b arbitrary: v)(auto simp: id_fresh_iff)

lemma max_id_geq_b: "v = max_id_bexpr 0 b \<Longrightarrow> (\<forall>x \<in> (fv_bexpr b). v \<ge> x)"
proof(induction b arbitrary: v)
  case (BLeq x1a x2a)
  then show ?case
    using max_id_geq by fastforce
qed auto

lemma id_suc_not_vars_b : "v = max_id_bexpr 0 b \<Longrightarrow> (v + 1) \<notin> (fv_bexpr b)"
proof(induction b arbitrary: v)
  case (BAnd b1 b2)
  then show ?case
    by (meson add_le_same_cancel1 max_id_geq_b not_one_le_zero)
next
  case (BLeq x1a x2a)
  then show ?case
    by (meson add_le_same_cancel1 max_id_geq_b not_one_le_zero)
qed auto


lemma max_plus_fresh_B : "v = max_id_bexpr 0 b \<Longrightarrow> fresh_in_bexpr (v + 1) b"
proof(induction b arbitrary: v)
  case (BAnd b1 b2)  
  then show ?case
    using id_fresh_iff_b id_suc_not_vars_b by presburger
next
  case (BLeq x1a x2a)
  then show ?case
    using id_fresh_iff_b id_suc_not_vars_b by presburger
qed auto

lemma id_fresh_iff_f : "v \<notin> vars_in_formula f \<Longrightarrow> fresh_in_formula v f"
proof(induction f arbitrary: v)
  case (FAll x f)
  then show ?case by(auto simp: vars_in_formula_def)
qed (auto simp: id_fresh_iff_b vars_in_formula_def)

lemma max_id_geq_f: "v = max_id_formula 0 f \<Longrightarrow> (\<forall>x \<in> (vars_in_formula f). v \<ge> x)"
proof(induction f arbitrary: v)
  case (FTerm x)
  then show ?case
    by (simp add: max_id_geq_b vars_in_formula_def)
next
  case (FAnd f1 f2)
  then show ?case  apply(simp add: vars_in_formula_def)
    by (metis Un_iff le_max_iff_disj)
next
  case (FNot f)
  then show ?case by(simp add: vars_in_formula_def)
next
  case (FImp f1 f2)
  then show ?case apply(simp add: vars_in_formula_def)
    by (metis Un_iff le_max_iff_disj)
next
  case (FAll x1a f)
  then show ?case apply(simp add: vars_in_formula_def)
    by force
qed




lemma id_suc_not_vars_f : "v = max_id_formula 0 f \<Longrightarrow> (v + 1) \<notin> (vars_in_formula f)"
proof(induction f arbitrary: v)
  case (FTerm x)
  then show ?case
    using max_id_geq_f by fastforce
next
  case (FAnd f1 f2)
  then show ?case
    by (metis add.commute add_le_same_cancel2 max_id_geq_f not_one_le_zero)
next
  case (FNot f)
  then show ?case
    by (simp add: vars_in_formula_def)
next
  case (FImp f1 f2)
  then show ?case
    by (metis add.commute add_le_same_cancel2 max_id_geq_f not_one_le_zero)
next
  case (FAll x1a f)
  then show ?case
    by (metis add.commute add_le_same_cancel2 max_id_geq_f not_one_le_zero)
qed


lemma fresh_var_is_fresh : "v = fresh_from f \<Longrightarrow> fresh_in_formula v f"
proof(induction f arbitrary: v)
  case (FTerm x)
  then show ?case
    using fresh_from_def id_fresh_iff_f id_suc_not_vars_f by presburger
next
  case (FAnd f1 f2)
  then show ?case
    using fresh_from_def id_fresh_iff_f id_suc_not_vars_f by presburger
next
  case (FNot f)
  then show ?case
    using fresh_from_def id_fresh_iff_f id_suc_not_vars_f by presburger
next
  case (FImp f1 f2)
  then show ?case
    using fresh_from_def id_fresh_iff_f id_suc_not_vars_f by presburger
next
  case (FAll x1a f)
  then show ?case
    using fresh_from_def id_fresh_iff_f id_suc_not_vars_f by presburger
qed

fun eval_formula :: "'a formula \<Rightarrow> 'a state \<Rightarrow> bool" where
  "eval_formula (FTerm b) st = eval_bexpr b st (Enormal True)"
| "eval_formula (FAnd f1 f2) st = (eval_formula f1 st \<and> eval_formula f2 st)"
| "eval_formula (FNot f) st = (\<not> (eval_formula f st))"
| "eval_formula (FImp f1 f2) st = (eval_formula f1 st \<longrightarrow> eval_formula f2 st)"
| "eval_formula (FAll y f) st = (\<forall> n. eval_formula f (st(y := Some n)))"


end