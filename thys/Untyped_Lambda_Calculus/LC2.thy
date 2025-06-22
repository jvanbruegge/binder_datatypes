theory LC2
  imports "Binders.MRBNF_Recursor"
begin

(* Source: James McKinna: https://www.macs.hw.ac.uk/splv/wp-content/uploads/2022/07/LambdaCalculus2-ChurchRosser.pdf *)

declare [[mrbnf_internals]]
binder_datatype 'a "term" =
  Var 'a
| App "'a term" "'a term"
| Lam x::'a t::"'a term" binds x in t
for
  vvsubst: rename
  tvsubst: subst








lemma fresh_cases:
  fixes e::"'a::var term"
  assumes "|A::'a set| <o |UNIV::'a set|"
  shows "(\<And>x. e = Var x \<Longrightarrow> P) \<Longrightarrow> (\<And>e1 e2. e = App e1 e2 \<Longrightarrow> P) \<Longrightarrow> (\<And>x e'. x \<notin> A \<Longrightarrow> e = Lam x e' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (rule term.TT_fresh_cases[OF assms, of e])
  apply (unfold Var_def App_def Lam_def)
  subgoal for x
    apply (rule Abs_term_pre_cases[of x])
    apply hypsubst
    subgoal for y
      apply (rule sum.exhaust[of y]; hypsubst)
       apply simp
      subgoal for y
        apply (rule sum.exhaust[of y]; hypsubst)
        by (auto simp: set2_term_pre_def sum.set_map prod.set_map Abs_term_pre_inverse)
      . .
    done
lemma singl_bound: "|{a}| <o |UNIV::'a::var set|"
  by (simp add: infinite_UNIV)
lemma Lam_inject_strong:
assumes "Lam (x::'a::var) e = Lam x' e'"
shows "\<exists>f. bij f \<and> |supp (f::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<and>
   id_on (- {x,x'}) f \<and> id_on (FVars_term (Lam x e)) f \<and>
   f x = x' \<and> permute_term f e = e'"
apply(rule exI[of _ "x \<leftrightarrow> x'"])
using assms unfolding term.inject apply auto
unfolding id_on_def apply (auto simp: infinite_UNIV supp_id_bound) by (metis swap_def)
lemma Lam_inject: "(Lam x e = Lam x' e') = (\<exists>f. bij f \<and> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<and> id_on (FVars_term (Lam x e)) f \<and> f x = x' \<and> permute_term f e = e')"
  by (metis Lam_inject_strong id_on_def term.permute(3) term.permute_cong_id)

abbreviation usubst :: "'a::var term \<Rightarrow> 'a \<Rightarrow> 'a term \<Rightarrow> 'a term" ("_[_ \<mapsto> _]" [60, 60, 60] 80) where
  "usubst e1 x e2 \<equiv> subst (Var(x := e2)) e1"

lemma SSupp_small[simp]: "|SSupp_term (Var(x::'a::var := e2))| <o |UNIV::'a set|"
  unfolding SSupp_term_def tvVVr_subst_def tv\<eta>_term_subst_def Var_def[symmetric] comp_def fun_upd_def
  by (auto simp: infinite_UNIV card_of_subset_bound[of _ "{x}"])

lemma FVars_subst[simp]:
  assumes "|SSupp_term (f::'a::var \<Rightarrow> _)| <o |UNIV::'a set|"
  shows "FVars_term (subst f e) = (\<Union>x\<in>FVars_term e. FVars_term (f x))"
using assms proof (binder_induction e avoiding: "IImsupp_term f" rule: term.strong_induct)
  case Bound
  then show ?case unfolding IImsupp_term_def using assms
    by (simp add: UN_bound term.set_bd_UNIV var_class.Un_bound)
qed (auto simp: term.IImsupp_Diff)

lemma usub_equiv[equiv,simp]:
  fixes \<sigma>::"'a::var \<Rightarrow> 'a"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|"
  shows "permute_term \<sigma> (e1[x \<mapsto> e2]) = permute_term \<sigma> e1[\<sigma> x \<mapsto> permute_term \<sigma> e2]"
proof (binder_induction e1 avoiding: x e2 rule: term.strong_induct)
  case (Lam x1 x2)
  then show ?case
      apply (subst term.subst)
    apply (rule SSupp_small)
     apply (auto simp: IImsupp_term_def SSupp_term_def tvVVr_subst_def tv\<eta>_term_subst_def Var_def[symmetric] assms)
    apply (subst term.subst)
      apply (rule SSupp_small)
     apply (auto simp: IImsupp_term_def SSupp_term_def tvVVr_subst_def tv\<eta>_term_subst_def Var_def[symmetric] assms bij_implies_inject term.FVars_permute)
    done
qed (auto simp: assms bij_implies_inject)

lemma not_ex_equiv[equiv]:
  fixes \<sigma>::"'a::var \<Rightarrow> 'a"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|"
  shows "\<nexists>x e. e\<^sub>2 = Lam x e \<Longrightarrow> \<nexists>x e. permute_term \<sigma> e\<^sub>2 = Lam x e"
  apply (rule fresh_cases[OF emp_bound, of e\<^sub>2])
  by (auto simp: assms)




inductive step :: "'a::var term \<Rightarrow> 'a term \<Rightarrow> bool" (infix "\<^bold>\<longrightarrow>\<^sub>\<beta>" 50) where
  Beta:                 "App (Lam x e1) e2 \<^bold>\<longrightarrow>\<^sub>\<beta> e1[x \<mapsto> e2]"
| AppL: "e1 \<^bold>\<longrightarrow>\<^sub>\<beta> e1' \<Longrightarrow> App e1 e2 \<^bold>\<longrightarrow>\<^sub>\<beta> App e1' e2"
| AppR: "e2 \<^bold>\<longrightarrow>\<^sub>\<beta> e2' \<Longrightarrow> App e1 e2 \<^bold>\<longrightarrow>\<^sub>\<beta> App e1 e2'"
| Xi:   "e \<^bold>\<longrightarrow>\<^sub>\<beta> e'   \<Longrightarrow> Lam x e \<^bold>\<longrightarrow>\<^sub>\<beta> Lam x e'"

inductive superparallel :: "'a::var term \<Rightarrow> 'a term \<Rightarrow> bool" (infix "\<equiv>\<ggreater>" 50) where
  Var: "Var x \<equiv>\<ggreater> Var x"
| Lam: "e\<^sub>1 \<equiv>\<ggreater> e\<^sub>2 \<Longrightarrow> Lam x e\<^sub>1 \<equiv>\<ggreater> Lam x e\<^sub>2"
| App: "e\<^sub>1 \<equiv>\<ggreater> e\<^sub>2 \<Longrightarrow> a\<^sub>1 \<equiv>\<ggreater> a\<^sub>2 \<Longrightarrow> App e\<^sub>1 a\<^sub>1 \<equiv>\<ggreater> App e\<^sub>2 a\<^sub>2"
| Beta: "e\<^sub>1 \<equiv>\<ggreater> Lam x e \<Longrightarrow> a\<^sub>1 \<equiv>\<ggreater> a \<Longrightarrow> App e\<^sub>1 a\<^sub>1 \<equiv>\<ggreater> e[x \<mapsto> a]"

inductive superdevelopment :: "'a::var term \<Rightarrow> 'a term \<Rightarrow> bool" (infix "\<equiv>\<ggreater>\<^sub>d" 50) where
  Var: "Var x \<equiv>\<ggreater>\<^sub>d Var x"
| Lam: "e\<^sub>1 \<equiv>\<ggreater>\<^sub>d e\<^sub>2 \<Longrightarrow> Lam x e\<^sub>1 \<equiv>\<ggreater>\<^sub>d Lam x e\<^sub>2"
| App: "e\<^sub>1 \<equiv>\<ggreater>\<^sub>d e\<^sub>2 \<Longrightarrow> \<nexists>x e. e\<^sub>2 = Lam x e \<Longrightarrow> a\<^sub>1 \<equiv>\<ggreater>\<^sub>d a\<^sub>2 \<Longrightarrow> App e\<^sub>1 a\<^sub>1 \<equiv>\<ggreater>\<^sub>d App e\<^sub>2 a\<^sub>2"
| Beta: "e\<^sub>1 \<equiv>\<ggreater>\<^sub>d Lam x e \<Longrightarrow> a\<^sub>1 \<equiv>\<ggreater>\<^sub>d a \<Longrightarrow> App e\<^sub>1 a\<^sub>1 \<equiv>\<ggreater>\<^sub>d e[x \<mapsto> a]"





lemmas [intro] = superparallel.intros
binder_inductive superparallel sorry

lemma par_LamE:
  assumes "x \<notin> FVars_term e"
  assumes "Lam x e\<^sub>1 \<equiv>\<ggreater> e" "\<And>e\<^sub>2. e = Lam x e\<^sub>2 \<Longrightarrow> e\<^sub>1 \<equiv>\<ggreater> e\<^sub>2 \<Longrightarrow> P"
  shows P
using assms(2) proof cases
  case (Lam e\<^sub>1' e\<^sub>2 y)
  then have "e\<^sub>1 \<equiv>\<ggreater> permute_term (x \<leftrightarrow> y) e\<^sub>2" using equiv(12)[OF bij_swap supp_swap_bound[OF infinite_UNIV]]
    by (metis swap_sym term.inject(3))
  moreover have "e = Lam x (permute_term (x \<leftrightarrow> y) e\<^sub>2)" using assms(1) by (simp add: local.Lam(2) swap_sym)
  ultimately show P using assms(3) by blast
qed auto

binder_inductive superdevelopment
  sorry
lemmas [intro] = superdevelopment.intros

lemma dev_imp_par: "e\<^sub>1 \<equiv>\<ggreater>\<^sub>d e\<^sub>2 \<Longrightarrow> e\<^sub>1 \<equiv>\<ggreater> e\<^sub>2"
  by (induction e\<^sub>1 e\<^sub>2 rule: superdevelopment.induct) auto

lemma par_refl[simp]: "e \<equiv>\<ggreater> e"
  by (induction e) auto

lemma beta_imp_par: "e\<^sub>1 \<^bold>\<longrightarrow>\<^sub>\<beta> e\<^sub>2 \<Longrightarrow> e\<^sub>1 \<equiv>\<ggreater> e\<^sub>2"
  by (induction e\<^sub>1 e\<^sub>2 rule: step.induct) auto

lemma dev_continue: "\<exists>e'. e \<equiv>\<ggreater>\<^sub>d e'"
  by (induction e) auto

(*lemma par_subst:
  fixes e1 e2::"'a::var term"
  assumes "Lam y e1 \<equiv>\<ggreater> Lam x e2" "a\<^sub>1 \<equiv>\<ggreater> a\<^sub>2"
  shows "e1[y \<mapsto> a\<^sub>1] \<equiv>\<ggreater> e2[x \<mapsto> a\<^sub>2]"
proof -
  obtain z where z: "z \<noteq> y" "z \<noteq> x" "z \<notin> FVars_term e1" "z \<notin> FVars_term e2"
    "z \<notin> FVars_term a\<^sub>1" "z \<notin> FVars_term a\<^sub>2"
    using exists_fresh[of "{x, y} \<union> FVars_term e1 \<union> FVars_term e2 \<union> FVars_term a\<^sub>1 \<union> FVars_term a\<^sub>2"]
    by (metis Un_iff emp_bound infinite_UNIV insertCI insert_bound term.set_bd_UNIV var_class.Un_bound)
  define e1' e2' where e': "e1' \<equiv> permute_term (y \<leftrightarrow> z) e1" "e2' \<equiv> permute_term (x \<leftrightarrow> z) e2"
  from z have "Lam z e1' \<equiv>\<ggreater> Lam z e2'" unfolding e'
    using assms(1) by (metis term.inject(3))
  have "e1'[z \<mapsto> permute_term (y \<leftrightarrow> z) a\<^sub>1] \<equiv>\<ggreater> e2'[z \<mapsto> permute_term (x \<leftrightarrow> z) a\<^sub>2]" sorry
  then show ?thesis unfolding e' using z*)

lemma triangle: "e\<^sub>1 \<equiv>\<ggreater>\<^sub>d e' \<Longrightarrow> e\<^sub>1 \<equiv>\<ggreater> e \<Longrightarrow> e \<equiv>\<ggreater> e'"
proof (binder_induction e\<^sub>1 e' arbitrary: e avoiding: e rule: superdevelopment.strong_induct)
  case (Var x e)
  then show ?case by cases auto
next
  case (Lam e\<^sub>1' e\<^sub>2 x e)
  obtain e2 where "e\<^sub>1' \<equiv>\<ggreater> e2" "e = Lam x e2" using par_LamE[OF Lam(1,3)] by auto
  then show ?case using Lam.IH by blast
next
  case (App e\<^sub>1' e\<^sub>2 a\<^sub>1 a\<^sub>2 e)
  from App(4) show ?case
  proof (binder_induction "App e\<^sub>1' a\<^sub>1" e avoiding: e\<^sub>1' rule: superparallel.strong_induct)
    case (App e\<^sub>1 e\<^sub>2' a\<^sub>1 a\<^sub>2')
    then show ?case by (simp add: App.IH(1,2) superparallel.App)
  next
    case (Beta e\<^sub>1 x e a\<^sub>1 a)
    then show ?case
      sorry
  qed auto
next
  case (Beta e\<^sub>1' x ea a\<^sub>1 a e)
  from Beta(4) show ?case
  proof (binder_induction "App e\<^sub>1' a\<^sub>1" e avoiding: e\<^sub>1' rule: superparallel.strong_induct)
    case (App e\<^sub>1 e\<^sub>2 a\<^sub>1 a\<^sub>2)
    then show ?case by (simp add: Beta.IH(1,2) superparallel.Beta)
  next
    case inner: (Beta e\<^sub>1 y e' a\<^sub>1' aa)
    have "Lam y e' \<equiv>\<ggreater> Lam x ea" using Beta.IH(1) inner.hyps(2,6) by auto
    moreover have "aa \<equiv>\<ggreater> a" using Beta.IH(2) inner.hyps(4,6) by auto
    ultimately show ?case using par_subst by blast
  qed auto
qed

end