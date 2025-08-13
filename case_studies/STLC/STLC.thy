theory STLC
  imports "Binders.MRBNF_Recursor" "HOL-Library.FSet"
begin

datatype \<tau> = Unit | Arrow \<tau> \<tau> (infixr "\<rightarrow>" 40)

declare [[mrbnf_internals]]

binder_datatype 'a terms =
  Var 'a
| App "'a terms" "'a terms"
| Abs x::'a \<tau> t::"'a terms" binds x in t
for
  vvsubst: vvsubst
  tvsubst: tvsubst

print_theorems

lemma Abs_inject: "(Abs x \<tau> e = Abs x' \<tau>' e') = (\<exists>f. bij f \<and> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<and> id_on (FVars_terms (Abs x \<tau> e)) f \<and> f x = x' \<and> \<tau> = \<tau>' \<and> permute_terms f e = e')"
  unfolding terms.set
  unfolding Abs_def terms.TT_inject0 map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_terms_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_terms_pre_def
    Un_empty_right UN_single
  apply (rule refl)
  done

lemma bij_map_terms_pre: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij (map_terms_pre (id::_::var \<Rightarrow> _) f (permute_terms f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_terms_pre id (inv f) (permute_terms (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 terms.permute_comp0 terms.permute_id0
  apply (rule terms_pre.map_id0)
  apply (rule trans)
   apply (rule terms_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 terms.permute_comp0 terms.permute_id0
  apply (rule terms_pre.map_id0)
  done

lemma map_terms_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> inv (map_terms_pre (id::_::var \<Rightarrow> _) f (permute_terms f) id) = map_terms_pre id (inv f) (permute_terms (inv f)) id"
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
  apply assumption
  apply (rule inv_unique_comp)
   apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
   defer
  apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 inv_o_simp2 terms.permute_comp0 terms.permute_id0 terms_pre.map_id0
   apply (rule refl)+
  done

lemma Abs_set3: "terms_ctor v = Abs x \<tau> e \<Longrightarrow> \<exists>x' e'. terms_ctor v = Abs x' \<tau> e' \<and> x' \<in> set2_terms_pre v \<and> e' \<in> set3_terms_pre v"
  unfolding Abs_def terms.TT_inject0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_terms_pre id f (permute_terms f) id"])
     apply (rule bij_map_terms_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding terms.permute_id0 terms_pre.map_id map_terms_pre_inv_simp
    unfolding map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_terms_pre_def set3_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding terms.FVars_permute[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF terms.permute_bij[OF bij_imp_bij_inv supp_inv_bound]]
  terms.permute_inv_simp[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding terms.permute_comp[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 terms.permute_id
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+
  done
  done

lemma Abs_avoid: "|A::'a::var set| <o |UNIV::'a set| \<Longrightarrow> \<exists>x' e'. Abs x \<tau> e = Abs x' \<tau> e' \<and> x' \<notin> A"
  apply (erule terms.TT_fresh_cases[of _ "Abs x \<tau> e"])
   apply (drule sym)
  apply (frule Abs_set3)
  apply (erule exE conjE)+
  apply (rule exI)+
  apply (rule conjI)
   apply (rule trans)
    apply (rule sym)
    apply assumption
  apply (rotate_tac 3)
   apply assumption
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

(* small step semantics *)
no_notation Set.member  ("(_/ : _)" [51, 51] 50)

definition fresh :: "'a::var \<Rightarrow> ('a * 'b) fset \<Rightarrow> bool" ("(_/ \<sharp> _)" [51, 51] 50) where
  "fresh x \<Gamma> \<equiv> x |\<notin>| fst |`| \<Gamma>"

lemma isin_rename: "bij f \<Longrightarrow> (f x, \<tau>) |\<in>| map_prod f id |`| \<Gamma> \<longleftrightarrow> (x, \<tau>) |\<in>| \<Gamma>"
  by (force simp: bij_implies_inject)

abbreviation extend :: "('a * \<tau>) fset \<Rightarrow> 'a::var \<Rightarrow> \<tau> \<Rightarrow> ('a * \<tau>) fset" ("(_,_:_)" [52, 52, 52] 53) where
  "extend \<Gamma> a \<tau> \<equiv> finsert (a, \<tau>) \<Gamma>"

inductive Step :: "'a::var terms \<Rightarrow> 'a terms \<Rightarrow> bool" (infixr "\<^bold>\<longrightarrow>" 25) where
  ST_Beta: "App (Abs x \<tau> e) e2 \<^bold>\<longrightarrow> tvsubst (Var(x:=e2)) e"
| ST_App: "e1 \<^bold>\<longrightarrow> e1' \<Longrightarrow> App e1 e2 \<^bold>\<longrightarrow> App e1' e2"

inductive Ty :: "('a::var * \<tau>) fset \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _ : _" [25, 25, 25] 26) where
  Ty_Var: "(x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y Var x : \<tau>"
| Ty_App: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y App e1 e2 : \<tau>\<^sub>2"
| Ty_Abs: "\<lbrakk> x \<sharp> \<Gamma> ; \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau> e : \<tau> \<rightarrow> \<tau>\<^sub>2"

lemma map_prod_comp0: "map_prod f1 f2 \<circ> map_prod f3 f4 = map_prod (f1 \<circ> f3) (f2 \<circ> f4)"
  using prod.map_comp by auto

lemma equiv[equiv]:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
    (* equivariance *)
    "(x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> (f x, \<tau>) |\<in>| map_prod f id |`| \<Gamma>"
    "x \<sharp> \<Gamma> \<Longrightarrow> f x \<sharp> map_prod f id |`| \<Gamma>"
    (* equivariance of extend *)
    "map_prod f id |`| (\<Gamma>,x:\<tau>) = (map_prod f id |`| \<Gamma>),f x:\<tau>"
    (* freshness *)
   apply (simp add: assms isin_rename)
  unfolding fresh_def
     apply force
  using assms(1) fimage_iff apply (fastforce simp: bij_implies_inject)
  apply simp
  done

binder_inductive Ty
  subgoal for R B x1 x2 x3
    apply (rule exI[of _ B])
    unfolding fresh_def by auto
  done

thm Ty.strong_induct
thm Ty.equiv

lemma provided:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
    (* equivariance *)
    "(x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> (f x, \<tau>) |\<in>| map_prod f id |`| \<Gamma>"
    "x \<sharp> \<Gamma> \<Longrightarrow> f x \<sharp> map_prod f id |`| \<Gamma>"
    (* equivariance of extend *)
    "map_prod f id |`| (\<Gamma>,x:\<tau>) = (map_prod f id |`| \<Gamma>),f x:\<tau>"
    (* freshness *)
    "\<lbrakk> x \<sharp> \<Gamma> ; \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<rbrakk> \<Longrightarrow> x \<notin> \<Union>(Basic_BNFs.fsts ` fset \<Gamma>)"
   apply (simp add: assms isin_rename)
  unfolding fresh_def
     apply force
  using assms(1) fimage_iff apply (fastforce simp: bij_implies_inject)
   apply simp
  using fimage_iff by fastforce

inductive_cases
  Ty_VarE[elim]: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Var x : \<tau>"
  and Ty_AppE[elim]: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y App e1 e2 : \<tau>\<^sub>2"
print_theorems

lemma provided_strong:
  fixes f::"'a::var \<Rightarrow> 'a" and \<Gamma>::"('a \<times> \<tau>) fset"
  shows "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> x \<sharp> \<Gamma> \<longleftrightarrow> f x \<sharp> map_prod f id |`| \<Gamma>"
  apply (rule iffI)
   apply (rule provided)
  apply assumption+
  apply (drule provided[rotated -1])
    apply (rule bij_imp_bij_inv)
  apply assumption
  apply (rule supp_inv_bound)
  apply assumption+
  unfolding inv_simp1 fset.map_comp comp_def prod.map_comp id_def
  unfolding id_def[symmetric] prod.map_id fset.map_id
  apply assumption
  done

lemma Ty_fresh_induct:
  fixes A::"'a::var set" and e::"'a terms"
  assumes "|A| <o |UNIV::'a set|" and x: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>"
    and Ty_Var: "\<And>x \<tau> \<Gamma>. (x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> P \<Gamma> (Var x) \<tau>"
    and Ty_App: "\<And>\<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2. \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 \<Longrightarrow> P \<Gamma> e1 (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<Longrightarrow> P \<Gamma> e2 \<tau>\<^sub>1 \<Longrightarrow> P \<Gamma> (App e1 e2) \<tau>\<^sub>2"
    and Ty_Abs: "\<And>x \<Gamma> \<tau> e \<tau>\<^sub>2. x \<notin> A \<union> fst ` fset \<Gamma> \<union> FVars_terms (Abs x \<tau> e) \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> P (\<Gamma>,x:\<tau>) e \<tau>\<^sub>2 \<Longrightarrow> P \<Gamma> (Abs x \<tau> e) (\<tau> \<rightarrow> \<tau>\<^sub>2)"
  shows "P \<Gamma> e \<tau>"
  using assms(2) apply (binder_induction \<Gamma> e \<tau> avoiding: A \<Gamma> e rule: Ty.strong_induct)
    using assms by auto

(* automate with binder_inductive_cases *)
lemma Ty_AbsE:
  fixes e::"'a::var terms" and A::"'a set"
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>" "|A| <o |UNIV::'a set|"
    and "\<And>y e' \<tau>' \<tau>\<^sub>2. y \<notin> A \<Longrightarrow> Abs x \<tau>\<^sub>1 e = Abs y \<tau>' e' \<Longrightarrow> \<tau> = (\<tau>' \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> y \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,y:\<tau>' \<turnstile>\<^sub>t\<^sub>y e' : \<tau>\<^sub>2 \<Longrightarrow> P"
  shows P
  apply (rule mp[OF Ty_fresh_induct[OF assms(2,1), of "\<lambda>\<Gamma>' e' \<tau>'. \<Gamma>' = \<Gamma> \<and> e' = Abs x \<tau>\<^sub>1 e \<and> \<tau>' = \<tau> \<longrightarrow> P"]])
     apply (rule impI, (erule conjE)+, rotate_tac -2, erule notE[rotated], rule terms.distinct)+
   apply (rule impI)
   apply (erule conjE)+
   apply hypsubst
  unfolding Un_iff de_Morgan_disj
   apply (erule conjE)+
   apply (rule assms(3))
       apply assumption
      apply (rule sym)
      apply assumption+
  apply (rule conjI refl)+
  done

lemma rename_Ty:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>' \<longleftrightarrow> map_prod f id |`| \<Gamma> \<turnstile>\<^sub>t\<^sub>y vvsubst f e : \<tau>'"
  apply (rule iffI)
  apply (unfold terms.vvsubst_permute[OF assms])
   apply (rule Ty.equiv)
     apply (rule assms)+
   apply assumption
  apply (drule Ty.equiv[rotated -1])
    apply (rule bij_imp_bij_inv)
    apply (rule assms)
   apply (rule supp_inv_bound)
    apply (rule assms)+
  unfolding terms.permute_comp[OF assms(1,2) bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]]
  terms.permute_id
    inv_o_simp1[OF assms(1)] terms.map_id map_prod.comp id_o map_prod.id fset.map_comp fset.map_id
  apply assumption
  done

lemma Ty_AbsE'':
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>" "x \<notin> \<Union>(Basic_BNFs.fsts ` fset \<Gamma>)"
and "\<And>\<tau>\<^sub>2. \<tau> = (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,x:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> P"
shows "P"
  apply (rule Ty_AbsE)
    apply (rule assms(1))
  apply (rule terms_pre.UN_bound)
    apply (rule ordLess_ordLeq_trans)
     apply (rule fset.set_bd)
          apply (rule terms.var_large)
   apply (rule ordLess_ordLeq_trans)
    apply (rule prod.set_bd)
   apply (rule terms.var_large)

  unfolding Abs_inject
  apply (erule exE conjE)+
  apply hypsubst

  apply (rule exE[OF ex_avoiding_bij])
          apply assumption+
        apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
       apply (rule terms.set_bd_UNIV)
      apply assumption
     apply (rule insert_bound[THEN iffD2])
     apply (rule emp_bound)
    apply (rule iffD2[OF disjoint_single])
  apply (rule assms(2))
apply (rule terms_pre.UN_bound)
         apply (rule ordLess_ordLeq_trans)
     apply (rule fset.set_bd)
          apply (rule terms.var_large)
   apply (rule ordLess_ordLeq_trans)
    apply (rule prod.set_bd)
   apply (rule terms.var_large)
  apply (erule conjE)+

  apply (rule assms(3))
    apply assumption
   apply (drule iffD1[OF arg_cong2[of _ _ _ _ "\<lambda>a b. a \<sharp> b"], rotated -1])
     apply (erule allE)
     apply (erule impE)
      prefer 2
      apply (rule sym)
      apply assumption
     apply (rule conjI)
      apply (rule UnI2)
      apply (rule singletonI)
     apply assumption
    prefer 2
    apply (rule iffD2[OF provided_strong])
      apply (rotate_tac -6)
      apply assumption+
 apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
  apply (drule trans[OF Int_commute])
       apply (unfold disjoint_iff)[1]
    apply (rule not_in_imsupp_same[symmetric])
    apply (erule allE)+
    apply (rotate_tac -1)
    apply (erule impE)
     apply (rule UN_I)
      apply assumption+
   apply (rule id_apply[symmetric])

  apply (rule iffD2[OF rename_Ty])
    apply (rotate_tac -5)
    apply assumption+
  unfolding provided
  apply (rule iffD2[OF arg_cong3[OF _ _ refl, of _ _ _ _ Ty], rotated -1])
    apply assumption
   apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ extend])
  apply (rule sym)
apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
  apply (drule trans[OF Int_commute])
       apply (unfold disjoint_iff)[1]
     apply (rule not_in_imsupp_same[symmetric])
     apply (rotate_tac -1)
     apply (erule allE)
     apply (erule impE)
      apply (rule UN_I)
       apply assumption+
    apply (rule id_apply[symmetric])
   apply (erule allE)
   apply (erule impE)
    prefer 2
    apply assumption
   apply (rule conjI)
    apply (rule UnI2)
    apply (rule singletonI)
   apply assumption
  apply (rule trans[rotated])
   apply (rule fun_cong[OF terms.vvsubst_permute])
    apply assumption+
  apply (rule terms.map_cong0)
    apply assumption+
  subgoal for y e' \<tau>' \<tau>2 f g z
    apply (rule case_split[of "z \<in> {x}"])
     apply (drule singletonD)
     apply hypsubst
     apply (erule allE)
     apply (erule impE)
      prefer 2
      apply assumption
     apply (rule conjI)
      apply (rule UnI2)
      apply (rule singletonI)
     apply assumption
    unfolding terms.set
    apply (drule id_onD, rule DiffI, assumption+)+
    apply (rule trans)
     apply assumption
    apply (rule sym)
    apply assumption
    done
  done
lemmas Ty_AbsE' = Ty_AbsE''[unfolded prod_sets_simps]

lemma context_invariance:
assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>'" "\<forall>x\<in>FVars_terms e. \<forall>\<tau>. (x, \<tau>) |\<in>| \<Gamma> \<longrightarrow> (x, \<tau>) |\<in>| \<Gamma>'"
shows "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y e : \<tau>'"
using assms proof (binder_induction \<Gamma> e \<tau>' arbitrary: \<Gamma>' avoiding: \<Gamma>' rule: Ty.strong_induct)
  case (Ty_Var x \<tau> \<Gamma> \<Gamma>')
  then show ?case by (auto intro: Ty.Ty_Var)
next
  case (Ty_App \<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2 \<Gamma>')
  then show ?case unfolding terms.set by (meson Ty.Ty_App UnI1 UnI2)
next
  case (Ty_Abs x \<Gamma> \<tau> e \<tau>\<^sub>2 \<Gamma>')
  then have "\<forall>y\<in>FVars_terms e. \<forall>\<tau>'. (y, \<tau>') |\<in>| \<Gamma>,x:\<tau> \<longrightarrow> (y, \<tau>') |\<in>| \<Gamma>',x:\<tau>"
    by (metis DiffI terms.set(3) fimageI finsert_iff fresh_def fst_conv fsts.cases prod_set_simps(1))
  moreover have "x \<sharp> \<Gamma>'" using Ty_Abs unfolding fresh_def by auto
  ultimately show ?case using Ty_Abs by (auto intro: Ty.Ty_Abs)
qed

lemma substitution: "\<lbrakk> \<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; x \<sharp> \<Gamma> ; {||} \<turnstile>\<^sub>t\<^sub>y v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (Var(x:=v)) e : \<tau>"
proof (binder_induction e arbitrary: \<Gamma> \<tau> avoiding: \<Gamma> x v rule: terms.strong_induct)
  case (Var a \<Gamma> \<tau>)
  then have 2: "(a, \<tau>) |\<in>| \<Gamma>,x:\<tau>'" by blast
  from \<open>{||} \<turnstile>\<^sub>t\<^sub>y v : \<tau>'\<close> have 3: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y v : \<tau>'" using context_invariance by blast
  then show ?case unfolding fun_upd_def apply (subst terms.subst)
    apply (smt (verit, ccfv_threshold) Field_card_of Prelim.insert_bound SSupp_def UNIV_cinfinite card_of_card_order_on
        card_of_subset_bound emp_bound insert_iff mem_Collect_eq subsetI)
  proof (cases "a = x")
    case True
    then have "\<tau> = \<tau>'" using 2 Var(1) unfolding fresh_def
      by (metis Var(2) Pair_inject finsertE fresh_def fst_eqD rev_fimage_eqI)
    then show "\<Gamma> \<turnstile>\<^sub>t\<^sub>y (if a = x then v else Var a) : \<tau>" using True 3 by simp
  next
    case False
    then have "(a, \<tau>) |\<in>| \<Gamma>" using 2 by blast
    then show "\<Gamma> \<turnstile>\<^sub>t\<^sub>y (if a = x then v else Var a) : \<tau>" using False Ty.Ty_Var by auto
  qed
next
  case (App e1 e2 \<Gamma> \<tau>)
  from App(3) obtain \<tau>\<^sub>1 where "\<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>" "\<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1" by blast
  then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (Var(x := v)) e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (Var(x := v)) e2 : \<tau>\<^sub>1" using App by blast+
  then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y App (tvsubst (Var(x := v)) e1) (tvsubst (Var(x := v)) e2) : \<tau>" using Ty_App by blast
  then show ?case by auto
next
  case (Abs y \<tau>\<^sub>1 e \<Gamma> \<tau>)
  then have 1: "y \<notin> IImsupp Var FVars_terms (Var(x:=v))" by (simp add: IImsupp_def SSupp_def)
  have "y \<notin> fst ` fset (\<Gamma>,x:\<tau>')" using Abs(1,2) unfolding fresh_def by auto
  then obtain \<tau>\<^sub>2 where 2: "(\<Gamma>,x:\<tau>'),y:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2" "\<tau> = (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2)" using Abs(5) Ty_AbsE' by metis
  moreover have "(\<Gamma>,x:\<tau>'),y:\<tau>\<^sub>1 = (\<Gamma>,y:\<tau>\<^sub>1),x:\<tau>'" by blast
  moreover have "x \<sharp> \<Gamma>,y:\<tau>\<^sub>1" using Abs(1,2,6) unfolding fresh_def by auto
  ultimately have "\<Gamma>,y:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y tvsubst (Var(x := v)) e : \<tau>\<^sub>2" using Abs(4,7) by metis
  moreover have "y \<sharp> \<Gamma>" using Abs(1) unfolding fresh_def by auto
  ultimately show ?case
    by (smt (verit, del_insts) "1" "2"(2) Abs.fresh(2) SSupp_def SSupp_fun_upd_Inj_bound Ty_Abs fun_upd_def mem_Collect_eq
        terms.subst(3))
qed

theorem progress: "{||} \<turnstile>\<^sub>t\<^sub>y e : \<tau> \<Longrightarrow> (\<exists>x \<tau> e'. e = Abs x \<tau> e') \<or> (\<exists>e'. e \<^bold>\<longrightarrow> e')"
proof (induction "{||} :: ('a::var * \<tau>) fset" e \<tau> rule: Ty.induct)
  case (Ty_App e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2)
  from Ty_App(2) show ?case using ST_Beta ST_App by blast
qed auto

theorem preservation: "\<lbrakk> {||} \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; e \<^bold>\<longrightarrow> e' \<rbrakk> \<Longrightarrow> {||} \<turnstile>\<^sub>t\<^sub>y e' : \<tau>"
proof (induction "{||} :: ('a::var * \<tau>) fset" e \<tau> arbitrary: e' rule: Ty.induct)
  case (Ty_App e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2)
  from Ty_App(5) show ?case
  proof cases
    case (ST_Beta x \<tau> e e2')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y App (Abs x \<tau> e) e2 : \<tau>\<^sub>2" using Ty_App Ty.Ty_App by fastforce
    have "{||} \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2" using Ty_App ST_Beta
      by (metis Ty_AbsE' \<tau>.inject all_not_fin_conv bot_fset.rep_eq image_is_empty terms.inject(2))
    then have "{||},x:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2" by (auto elim: Ty_AbsE')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y tvsubst (Var(x := e2')) e : \<tau>\<^sub>2" using substitution ST_Beta(1) Ty_App(3) unfolding fresh_def by fastforce
    then show ?thesis using ST_Beta by simp
  next
    case (ST_App e e1' e2')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y e1' : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2" using Ty_App by simp
    then show ?thesis using Ty_App Ty.Ty_App ST_App by fastforce
  qed
next
  case (Ty_Abs x \<tau> e \<tau>\<^sub>2)
  from \<open>Abs x \<tau> e \<^bold>\<longrightarrow> e'\<close> show ?case by cases auto
qed auto

end
