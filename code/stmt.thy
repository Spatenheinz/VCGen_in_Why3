theory stmt
  imports formula
begin

datatype 'a stmt =
  SSkip
  | SSeq "'a stmt" "'a stmt" 
  | Sassign 'a "'a aexpr"
  | Sassert "'a formula"
  | SIf "'a bexpr" "'a stmt" "'a stmt"
  | Swhile "'a bexpr" "'a formula" "'a stmt"

fun subst_aexpr :: "int aexpr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int aexpr" where
  "subst_aexpr (Cst n) x v = (Cst n)"
| "subst_aexpr (Var y) x v = (if x = y then Var v else Var y)"
| "subst_aexpr (BinOp a1 op a2) x v = BinOp (subst_aexpr a1 x v) op (subst_aexpr a2 x v)"

fun subst_bexpr :: "int bexpr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int bexpr" where
  "subst_bexpr (BCst b) x v = BCst b"
| "subst_bexpr (BLeq a1 a2) x v = BLeq (subst_aexpr a1 x v) (subst_aexpr a2 x v)"
| "subst_bexpr (BAnd b1 b2) x v = BAnd (subst_bexpr b1 x v) (subst_bexpr b2 x v)"
| "subst_bexpr (BNot b) x v = BNot (subst_bexpr b x v)"

fun subst_formula :: "int formula \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int formula" where
  "subst_formula (FTerm b) x v = FTerm (subst_bexpr b x v)"
| "subst_formula (FAnd f1 f2) x v = FAnd (subst_formula f1 x v) (subst_formula f2 x v)"
| "subst_formula (FNot f) x v = FNot (subst_formula f x v)"
| "subst_formula (FImp f1 f2) x v = FImp (subst_formula f1 x v) (subst_formula f2 x v)"
| "subst_formula (FAll y f) x v = FAll y (subst_formula f x v)"

fun abstract_effects :: "int stmt \<Rightarrow> int formula \<Rightarrow> int formula" where
   "abstract_effects SSkip f = f"
 | "abstract_effects (Sassert _) f = f"
 | "abstract_effects (SSeq s1 s2) f = abstract_effects s2 (abstract_effects s1 f)"
 | "abstract_effects (SIf _ s1 s2) f = abstract_effects s2 (abstract_effects s1 f)"
 | "abstract_effects (Sassign x _) f = (let v = fresh_from f in
                                        let f' = subst_formula f x v in
                                        FAll v f')" 
 | "abstract_effects (Swhile _ _ s) f = abstract_effects s f"

definition formula_equiv_sem :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> bool" (infixl "\<approx>" 40) where
  "f1 \<approx> f2 \<longleftrightarrow> (\<forall>st. eval_formula f1 st = eval_formula f2 st)"


(*lemma subst_not_occur : "x \<notin> vars_in_formula f \<Longrightarrow> eval_formula (FAll *)
lemma fall_elim : 
  assumes "x \<notin> fv_formula f"
  and "eval_formula (FAll v f) st"
  shows "eval_formula (subst_formula f v x) st"
  using assms oops

lemma subst_then_no_vars : "x \<noteq> v \<Longrightarrow> f' = (subst_formula f x v) \<Longrightarrow> x \<notin> fv_formula f'"
  oops

lemma abstract_effects_specialize : "eval_formula (abstract_effects s f) st \<Longrightarrow> eval_formula f st"
proof(induction s arbitrary: f st)
  case SSkip
  then show ?case by simp
next
  case (SSeq s1 s2)
  then show ?case
    by (metis abstract_effects.simps(3))
next
  case (Sassign x a)
  then show ?case apply(auto simp: Let_def) sorry
next
  case (Sassert x)
  then show ?case by simp
next
  case (SIf x1 s1 s2)
  then show ?case
    by (metis abstract_effects.simps(4))
next
  case (Swhile x1 x2 s)
  then show ?case
    by (metis abstract_effects.simps(6))
qed

lemma abstract_effects_distrib_conj :
  "(eval_formula (abstract_effects s p) st \<and> eval_formula (abstract_effects s q) st) \<Longrightarrow>
  eval_formula (abstract_effects s (FAnd p q)) st"
proof(induction s arbitrary: p q)
  case (SSeq s1 s2)
  then show ?case apply(simp) sorry
next
  case (Sassign x1 x2)
  then show ?case sorry
next
  case (SIf x1 s1 s2)
  then show ?case sorry
qed simp_all

definition valid_formula :: "'a formula \<Rightarrow> bool" where
  "valid_formula f \<longleftrightarrow> (\<forall> st. eval_formula f st)"

lemma abstract_effects_monotonic :
  "valid_formula (FImp p q) \<Longrightarrow>
   eval_formula (abstract_effects s p) st \<Longrightarrow>
   eval_formula (abstract_effects s q) st"
proof(induction s arbitrary: p q st)
  case (SSeq s1 s2)
  then show ?case apply(simp add: valid_formula_def) by blast
next
  case (Sassign x1 x2)
  then show ?case apply(simp add: valid_formula_def Let_def) sorry
next
  case (SIf x1 s1 s2)
  then show ?case apply(auto simp: valid_formula_def) by blast
qed (auto simp: valid_formula_def)

fun wp :: "int stmt \<Rightarrow> int formula \<Rightarrow> int formula" where
  "wp SSkip q = q"
| "wp (SSeq s1 s2) q = wp s1 (wp s2 q)"
| "wp (Sassert p) q = FAnd p (FImp p q)"
| "wp (Sassign x e) q = (let y = fresh_from q in
                        FAll y (FImp (FAnd (FTerm (BLeq (Var y) e))
                                           (FTerm (BLeq e (Var y))))
                               (subst_formula q x y)))"
| "wp (SIf b s1 s2) q = FAnd (FImp (FTerm b) (wp s1 q))
                             (FImp (FNot (FTerm b)) (wp s2 q))"
| "wp (Swhile cond invariant body) q =
   FAnd invariant
        (abstract_effects body
        (FAnd (FImp (FAnd (FTerm cond) invariant) (wp body invariant))
              (FImp (FAnd (FNot (FTerm cond)) invariant) q)))"

lemma abstract_effect_writes :
  "eval_formula (abstract_effects s q) st \<Longrightarrow>
   eval_formula (wp s (abstract_effects s q)) st"
proof(induction s arbitrary: q)
  case SSkip
  then show ?case by simp
next
  case (SSeq s1 s2)
  then show ?case sorry
next
  case (Sassign x1 x2)
  then show ?case sorry
next
  case (Sassert x)
  then show ?case sorry
next
  case (SIf x1 s1 s2)
  then show ?case sorry
next
  case (Swhile x1 x2 s)
  then show ?case sorry
qed


lemma monotonicity : "valid_formula (FImp p q) \<Longrightarrow>
  valid_formula (FImp (wp s p) (wp s q))"
proof(induction s arbitrary: p q)
  case (SSeq s1 s2)
  then show ?case
    using wp.simps(2) by presburger
next
  case (Sassign x1 x2)
  then show ?case
    by (metis abstract_effect_writes abstract_effects.simps(2) eval_formula.simps(2) valid_formula_def wp.simps(3))
next
  case (Swhile x1 x2 s)
  then show ?case
    by (metis abstract_effect_writes abstract_effects.simps(2) eval_formula.simps(2) valid_formula_def wp.simps(3))
qed (simp_all add: valid_formula_def)

lemma distrib_conj : 
  "eval_formula (wp s p) st \<and> eval_formula (wp s q) st \<Longrightarrow>
   eval_formula (wp s (FAnd p q)) st"
proof(induction s arbitrary: p q st)
  case (SSeq s1 s2)
  then show ?case
    by (metis abstract_effect_writes abstract_effects.simps(2) eval_formula.simps(2) wp.simps(3))
next
  case (Sassign x1 x2)
  then show ?case
    by (metis abstract_effect_writes abstract_effects.simps(2) eval_formula.simps(2) wp.simps(3))
next
  case (Swhile x1 x2 s)
  then show ?case
    by (metis abstract_effect_writes abstract_effects.simps(2) eval_formula.simps(2) wp.simps(3))
qed simp_all

end