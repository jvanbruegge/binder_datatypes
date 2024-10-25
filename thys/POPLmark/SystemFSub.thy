(* System F with SubsftypePing  *)
theory SystemFSub
  imports "SystemFSub_Types"
begin

abbreviation in_context :: "var \<Rightarrow> sftype \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ <: _ \<in> _" [55,55,55] 60) where
  "x <: t \<in> \<Gamma> \<equiv> (x, t) \<in> set \<Gamma>"
abbreviation well_scoped :: "sftype \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ closed'_in _" [55, 55] 60) where
  "well_scoped S \<Gamma> \<equiv> FFVars_sftypeP S \<subseteq> dom \<Gamma>"

inductive wf :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> bool"  where
  wf_Nil[intro]: "wf []"
| wf_Cons[intro!]: "\<lbrakk> x \<notin> dom \<Gamma> ; T closed_in \<Gamma> ; wf \<Gamma>\<rbrakk> \<Longrightarrow> wf (\<Gamma>,,x<:T)"

inductive_cases
  wfE[elim]: "wf \<Gamma>"
  and wf_ConsE[elim!]: "wf (a#\<Gamma>)"
print_theorems

lemma in_context_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "x <: T \<in> \<Gamma> \<Longrightarrow> f x <: rrename_sftypeP f T \<in> map_context f \<Gamma>"
  using assms unfolding map_context_def by auto

lemma extend_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "map_context f (\<Gamma>,,x<:T) = map_context f \<Gamma>,,f x <: rrename_sftypeP f T"
  using assms unfolding map_context_def by simp

lemma closed_in_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "S closed_in \<Gamma> \<Longrightarrow> rrename_sftypeP f S closed_in map_context f \<Gamma>"
  using assms by (auto simp: sftypeP.FFVars_rrenames)

lemma wf_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "wf \<Gamma> \<Longrightarrow> wf (map_context f \<Gamma>)"
unfolding map_context_def proof (induction \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case using assms apply auto
    apply (metis fst_conv image_iff)
    using closed_in_eqvt map_context_def by fastforce
qed simp

abbreviation Tsupp :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> sftype \<Rightarrow> sftype \<Rightarrow> var set" where
  "Tsupp \<Gamma> T\<^sub>1 T\<^sub>2 \<equiv> dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<union> FFVars_sftypeP T\<^sub>1 \<union> FFVars_sftypeP T\<^sub>2"

lemma small_Tsupp: "small (Tsupp \<Gamma> T\<^sub>1 T\<^sub>2)"
  by (auto simp: small_def sftypeP.card_of_FFVars_bounds sftypeP.Un_bound var_sftypeP_pre_class.UN_bound set_bd_UNIV sftypeP.set_bd)

lemma fresh: "\<exists>xx. xx \<notin> Tsupp \<Gamma> T\<^sub>1 T\<^sub>2"
  by (metis emp_bound equals0D imageI inf.commute inf_absorb2 small_Tsupp small_def small_isPerm subsetI)

lemma swap_idemp[simp]: "id(X := X) = id" by auto
lemma swap_left: "(id(X := Y, Y := X)) X = Y" by simp

lemma wf_FFVars: "wf \<Gamma> \<Longrightarrow> X \<in> FFVars_ctxt \<Gamma> \<Longrightarrow> X \<in> dom \<Gamma>"
  by (induction \<Gamma>) auto

lemma finite_Tsupp: "finite (Tsupp \<Gamma> T\<^sub>1 T\<^sub>2)"
  using finite_iff_le_card_var small_Tsupp small_def by meson

lemma exists_fresh:
"\<exists> Z. Z \<notin> set Zs \<and> Z \<notin> Tsupp \<Gamma> T\<^sub>1 T\<^sub>2"
proof-
  have 0: "|set Zs \<union> Tsupp \<Gamma> T\<^sub>1 T\<^sub>2| <o |UNIV::var set|"
  unfolding ls_UNIV_iff_finite
  using finite_Tsupp by blast
  then obtain Z where "Z \<notin> set Zs \<union> Tsupp \<Gamma> T\<^sub>1 T\<^sub>2"
  by (meson exists_fresh)
  thus ?thesis by auto
qed

(* *)

inductive ty :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> sftype \<Rightarrow> sftype \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [55,55,55] 60) where
  SA_Top: "\<lbrakk>wf \<Gamma>; S closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_Refl_TVar: "\<lbrakk>wf \<Gamma>; TVr x closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TVr x <: TVr x"
| SA_Trans_TVar: "\<lbrakk> X<:U \<in> \<Gamma> ; \<Gamma> \<turnstile> U <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TVr X <: T"
| SA_Arrow: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_All: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma>,, X<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<forall>X<:S\<^sub>1. S\<^sub>2 <: \<forall>X<:T\<^sub>1 .T\<^sub>2"

inductive_cases
  SA_TopE[elim!]: "\<Gamma> \<turnstile> Top <: T"
and
  SA_TVarE: "\<Gamma> \<turnstile> S <: TVr Z"
and
  SA_ArrER: "\<Gamma> \<turnstile> S <: T\<^sub>1 \<rightarrow> T\<^sub>2"
and
  SA_ArrEL: "\<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T "
and
  SA_AllER: "\<Gamma> \<turnstile> S <: \<forall>Z<:T\<^sub>1. T\<^sub>2"
and
  SA_AllEL: "\<Gamma> \<turnstile> \<forall>Z<:S\<^sub>1. S\<^sub>2 <: T "


lemma wf_context: "\<Gamma> \<turnstile> S <: T \<Longrightarrow> wf \<Gamma>"
  by (induction \<Gamma> S T rule: ty.induct)

lemma ty_fresh_extend: "\<Gamma>,, x <: U \<turnstile> S <: T \<Longrightarrow> x \<notin> dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<and> x \<notin> FFVars_sftypeP U"
by (metis (no_types, lifting) UnE fst_conv snd_conv subsetD wf_ConsE wf_FFVars wf_context)

make_binder_inductive ty
  subgoal for R B \<sigma> \<Gamma> T1 T2
    unfolding split_beta
    by (elim disj_forward exE)
      (auto simp add: isPerm_def supp_inv_bound map_context_def[symmetric] sftypeP_vvsubst_rrename
        sftypeP.rrename_comps sftypeP.FFVars_rrenames wf_eqvt extend_eqvt
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "rrename_sftypeP \<sigma> _"])+, (rule conjI)?, rule in_context_eqvt))+
  subgoal premises prems for R B \<Gamma> T1 T2
    using prems
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    apply (elim disj_forward exE; clarsimp)
     apply (((rule exI, rule conjI[rotated], assumption) |
          (((rule exI conjI)+)?, rule Forall_rrename) |
          (auto))+) []
    subgoal premises prems for T\<^sub>1 S\<^sub>1 X S\<^sub>2 T\<^sub>2
      using prems(3-)
      using exists_fresh[of "[X]" \<Gamma> T1 T2] apply(elim exE conjE)
      subgoal for Z
        apply (rule exI)
        apply (rule exI[of _ "{Z}"])
        apply (intro exI conjI)
              apply (rule refl)+
            apply (rule Forall_swap)
            apply simp
           apply (rule Forall_swap)
           apply simp
          apply assumption+
         apply (frule prems(1)[rule_format, of "(\<Gamma>,, X <: T\<^sub>1)" "S\<^sub>2" "T\<^sub>2"])
         apply (drule prems(2)[rule_format, of "id(X := Z, Z := X)" "\<Gamma>,, X <: T\<^sub>1" "S\<^sub>2" "T\<^sub>2", rotated 2])
           apply (auto simp: extend_eqvt)
        apply(rule cong[OF cong[OF cong], THEN iffD1, of R , OF refl, rotated -1, 
          of _ "rrename_sftypeP (id(X := Z, Z := X)) S\<^sub>2"]) 
          apply (drule ty_fresh_extend)
          apply (simp_all add: supp_swap_bound)
          by (metis (no_types, opaque_lifting) image_iff map_context_def map_context_swap_FFVars)
      done
    done
  done

thm ty.strong_induct

end
