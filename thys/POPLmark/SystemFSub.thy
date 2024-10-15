(* System F with Subtyping  *)
theory SystemFSub
  imports "Binders.MRBNF_Recursor"
    "Binders.Generic_Barendregt_Enhanced_Rule_Induction"
    "Prelim.Curry_LFP"
    "Prelim.FixedCountableVars"
    "Labeled_FSet"
begin

declare bij_swap[simp]
declare supp_id_bound[simp]

(*type_synonym label = nat*)

declare [[mrbnf_internals]]
binder_datatype 'a "typ" =
    TyVar 'a
  | Top
  | Fun "'a typ" "'a typ"
  | Forall X::'a "'a typ" T::"'a typ" binds X in T

instance var :: var_typ_pre apply standard
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)

declare supp_swap_bound[OF cinfinite_imp_infinite[OF typ.UNIV_cinfinite], simp]
declare typ.rrename_ids[simp] typ.rrename_id0s[simp]

lemma rrename_typ_simps[simp]:
  fixes f::"'a::var_typ_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
    "rrename_typ f (TyVar X) = TyVar (f X)"
    "rrename_typ f Top = Top"
    "rrename_typ f (Fun t1 t2) = Fun (rrename_typ f t1) (rrename_typ f t2)"
    "rrename_typ f (Forall Y T1 T2) = Forall (f Y) (rrename_typ f T1) (rrename_typ f T2)"
     apply (unfold TyVar_def Top_def Fun_def Forall_def)
     apply (rule trans)
      apply (rule typ.rrename_cctors)
       apply (rule assms)+
     defer
     apply (rule trans)
      apply (rule typ.rrename_cctors)
       apply (rule assms)+
     defer
     apply (rule trans)
      apply (rule typ.rrename_cctors)
       apply (rule assms)+
     defer
     apply (rule trans)
      apply (rule typ.rrename_cctors)
       apply (rule assms)+
     defer
     apply (unfold map_typ_pre_def comp_def Abs_typ_pre_inverse[OF UNIV_I] map_sum.simps
        map_prod_simp id_def
      )
     apply (rule refl)+
  done

lemma typ_inject:
  "TyVar X = TyVar Y \<longleftrightarrow> X = Y"
  "Fun T1 T2 = Fun R1 R2 \<longleftrightarrow> T1 = R1 \<and> T2 = R2"
  "Forall X T1 T2 = Forall Y R1 R2 \<longleftrightarrow> 
   T1 = R1 \<and> (\<exists>f. bij (f::'a::var_typ_pre \<Rightarrow> 'a) \<and> 
   |supp f| <o |UNIV::'a set| \<and> id_on (FFVars_typ T2 - {X}) f \<and> f X = Y \<and> rrename_typ f T2 = R2)"
    apply (unfold TyVar_def Fun_def Forall_def typ.TT_injects0
      set3_typ_pre_def comp_def Abs_typ_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_typ_pre_def
      prod.map_id set2_typ_pre_def prod_set_simps prod.set_map UN_single Abs_typ_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp
    )
  by auto
declare typ_inject(1,2)[simp]

corollary Forall_inject_same[simp]: "Forall X T1 T2 = Forall X S1 S2 \<longleftrightarrow> T1 = S1 \<and> T2 = S2"
  using typ_inject(3) typ.rrename_cong_ids
  by (metis (no_types, lifting) Diff_empty Diff_insert0 id_on_insert insert_Diff)

lemma Forall_rrename:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|" shows "
 (\<And>Y. Y\<in>FFVars_typ T2 - {X::'a::var_typ_pre} \<Longrightarrow> \<sigma> Y = Y) \<Longrightarrow> Forall X T1 T2 = Forall (\<sigma> X) T1 (rrename_typ \<sigma> T2)"
  apply (unfold Forall_def)
  apply (unfold typ.TT_injects0)
  apply (unfold set3_typ_pre_def set2_typ_pre_def comp_def Abs_typ_pre_inverse[OF UNIV_I] map_sum.simps
    map_prod_simp sum_set_simps prod_set_simps cSup_singleton Un_empty_left Un_empty_right
    Union_empty image_insert image_empty map_typ_pre_def id_def)
  apply (rule exI[of _ \<sigma>])
  apply (rule conjI assms)+
   apply (unfold id_on_def atomize_all atomize_imp)[1]
   apply (rule impI)
   apply assumption
  apply (rule refl)
  done

lemma Forall_swap: "y \<notin> FFVars_typ T2 - {x} \<Longrightarrow> Forall (x::'a::var_typ_pre) T1 T2 = Forall y T1 (rrename_typ (id(x:=y,y:=x)) T2)"
  apply (rule trans)
   apply (rule Forall_rrename)
     apply (rule bij_swap[of x y])
    apply (rule supp_swap_bound)
    apply (rule cinfinite_imp_infinite[OF typ.UNIV_cinfinite])
  by auto


type_synonym type = "var typ"
type_synonym \<Gamma>\<^sub>\<tau> = "(var \<times> type) list"

definition map_context :: "(var \<Rightarrow> var) \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>" where
  "map_context f \<equiv> map (map_prod f (rrename_typ f))"

abbreviation FFVars_ctxt :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var set" where
  "FFVars_ctxt xs \<equiv> \<Union>(FFVars_typ ` snd ` set xs)"
abbreviation extend :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau>" ("_ ,, _ <: _" [57,75,75] 71) where
  "extend \<Gamma> x T \<equiv> (x, T)#\<Gamma>"
abbreviation concat :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>" (infixl "(,,)" 71) where
  "concat \<Gamma> \<Delta> \<equiv> \<Delta> @ \<Gamma>"
abbreviation empty_context :: "\<Gamma>\<^sub>\<tau>" ("\<emptyset>") where "empty_context \<equiv> []"
abbreviation dom :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var set" where "dom xs \<equiv> fst ` set xs"
abbreviation disjoint :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" (infixl "(\<bottom>)" 71) where
  "disjoint \<Gamma> \<Delta> \<equiv> dom \<Gamma> \<inter> dom \<Delta> = {}"

lemma map_context_id[simp]: "map_context id = id"
  unfolding map_context_def by simp
lemma map_context_comp0[simp]:
  assumes "bij f" "|supp f| <o |UNIV::var set|" "bij g" "|supp g| <o |UNIV::var set|"
  shows "map_context f \<circ> map_context g = map_context (f \<circ> g)"
  apply (rule ext)
  unfolding map_context_def
  using assms by (auto simp: typ.rrename_comps)
lemmas map_context_comp = trans[OF comp_apply[symmetric] fun_cong[OF map_context_comp0]]
declare map_context_comp[simp]
lemma context_dom_set[simp]:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "dom (map_context f xs) = f ` dom xs"
  unfolding map_context_def by force
lemma set_bd_UNIV: "|set xs| <o |UNIV::var set|"
  apply (rule ordLess_ordLeq_trans)
    apply (tactic \<open>resolve_tac @{context} (BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name list}))) 1\<close>)
  apply (rule var_typ_pre_class.large)
  done
lemma context_set_bd_UNIV[simp]: "|dom xs| <o |UNIV::var set|"
  apply (rule ordLeq_ordLess_trans[OF card_of_image])
  apply (rule set_bd_UNIV)
  done
lemma context_map_cong_id:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  and "\<And>a. a \<in> dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<Longrightarrow> f a = a"
shows "map_context f \<Gamma> = \<Gamma>"
  unfolding map_context_def
  apply (rule trans)
   apply (rule list.map_cong0[of _ _ id])
   apply (rule trans)
    apply (rule prod.map_cong0[of _ _ id _ id])
  using assms by (fastforce intro!: typ.rrename_cong_ids)+

notation Fun (infixr "\<rightarrow>" 65)
notation Forall ("\<forall> _ <: _ . _" [62, 62, 62] 70)

abbreviation in_context :: "var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ <: _ \<in> _" [55,55,55] 60) where
  "x <: t \<in> \<Gamma> \<equiv> (x, t) \<in> set \<Gamma>"
abbreviation well_scoped :: "type \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ closed'_in _" [55, 55] 60) where
  "well_scoped S \<Gamma> \<equiv> FFVars_typ S \<subseteq> dom \<Gamma>"

hide_const wf
inductive wf :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> bool"  where
  wf_Nil[intro]: "wf []"
| wf_Cons[intro!]: "\<lbrakk> x \<notin> dom \<Gamma> ; T closed_in \<Gamma> ; wf \<Gamma>\<rbrakk> \<Longrightarrow> wf (\<Gamma>,,x<:T)"

inductive_cases
  wfE[elim]: "wf \<Gamma>"
  and wf_ConsE[elim!]: "wf (a#\<Gamma>)"
print_theorems

lemma in_context_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "x <: T \<in> \<Gamma> \<Longrightarrow> f x <: rrename_typ f T \<in> map_context f \<Gamma>"
  using assms unfolding map_context_def by auto

lemma extend_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "map_context f (\<Gamma>,,x<:T) = map_context f \<Gamma>,,f x <: rrename_typ f T"
  using assms unfolding map_context_def by simp

lemma closed_in_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "S closed_in \<Gamma> \<Longrightarrow> rrename_typ f S closed_in map_context f \<Gamma>"
  using assms by (auto simp: typ.FFVars_rrenames)

lemma wf_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "wf \<Gamma> \<Longrightarrow> wf (map_context f \<Gamma>)"
unfolding map_context_def proof (induction \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case using assms apply auto
    apply (metis fst_conv image_iff)
    using closed_in_eqvt map_context_def by fastforce
qed simp

abbreviation Tsupp :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> type \<Rightarrow> type \<Rightarrow> var set" where
  "Tsupp \<Gamma> T\<^sub>1 T\<^sub>2 \<equiv> dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<union> FFVars_typ T\<^sub>1 \<union> FFVars_typ T\<^sub>2"

lemma small_Tsupp: "small (Tsupp \<Gamma> T\<^sub>1 T\<^sub>2)"
  by (auto simp: small_def typ.card_of_FFVars_bounds typ.Un_bound var_typ_pre_class.UN_bound set_bd_UNIV typ.set_bd)

lemma fresh: "\<exists>xx. xx \<notin> Tsupp \<Gamma> T\<^sub>1 T\<^sub>2"
  by (metis emp_bound equals0D imageI inf.commute inf_absorb2 small_Tsupp small_def small_isPerm subsetI)

lemma swap_idemp[simp]: "id(X := X) = id" by auto
lemma swap_left: "(id(X := Y, Y := X)) X = Y" by simp

lemma wf_FFVars: "wf \<Gamma> \<Longrightarrow> X \<in> FFVars_ctxt \<Gamma> \<Longrightarrow> X \<in> dom \<Gamma>"
  by (induction \<Gamma>) auto

lemma finite_Tsupp: "finite (Tsupp \<Gamma> T\<^sub>1 T\<^sub>2)"
  using finite_iff_le_card_var small_Tsupp small_def by meson

lemma ls_UNIV_iff_finite: "|A| <o |UNIV::var set| \<longleftrightarrow> finite A"
using finite_iff_le_card_var by blast

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

lemma rrename_swap_FFvars[simp]: "X \<notin> FFVars_typ T \<Longrightarrow> Y \<notin> FFVars_typ T \<Longrightarrow>
  rrename_typ (id(X := Y, Y := X)) T = T"
apply(rule typ.rrename_cong_ids) by auto

lemma map_context_swap_FFVars[simp]:
"\<forall>k\<in>set \<Gamma>. X \<noteq> fst k \<and> X \<notin> FFVars_typ (snd k) \<and>
           Y \<noteq> fst k \<and> Y \<notin> FFVars_typ (snd k) \<Longrightarrow>
    map_context (id(X := Y, Y := X)) \<Gamma> = \<Gamma>"
  unfolding map_context_def apply(rule map_idI) by auto

lemma isPerm_swap: "isPerm (id(X := Y, Y := X))"
  unfolding isPerm_def by (auto simp: supp_swap_bound infinite_UNIV)

(* *)

inductive ty :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [55,55,55] 60) where
  SA_Top: "\<lbrakk>wf \<Gamma>; S closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_Refl_TVar: "\<lbrakk>wf \<Gamma>; TyVar x closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: TyVar x"
| SA_Trans_TVar: "\<lbrakk> X<:U \<in> \<Gamma> ; \<Gamma> \<turnstile> U <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar X <: T"
| SA_Arrow: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_All: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma>,, X<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<forall>X<:S\<^sub>1. S\<^sub>2 <: \<forall>X<:T\<^sub>1 .T\<^sub>2"

inductive_cases
  SA_TopE[elim!]: "\<Gamma> \<turnstile> Top <: T"
and
  SA_TVarE: "\<Gamma> \<turnstile> S <: TyVar Z"
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

lemma well_scoped:
  assumes "\<Gamma> \<turnstile> S <: T"
  shows "S closed_in \<Gamma>" "T closed_in \<Gamma>"
using assms proof (induction \<Gamma> S T rule: ty.induct)
case (SA_Trans_TVar x U \<Gamma> T) {
  case 1 then show ?case using SA_Trans_TVar
    by (metis fst_conv imageI singletonD subsetI typ.set(1))
next
  case 2 then show ?case using SA_Trans_TVar by simp
} qed auto

declare ty.intros[intro]

lemma ty_fresh_extend: "\<Gamma>,, x <: U \<turnstile> S <: T \<Longrightarrow> x \<notin> dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<and> x \<notin> FFVars_typ U"
  by (metis (no_types, lifting) UnE fst_conv snd_conv subsetD wf_ConsE wf_FFVars wf_context)

make_binder_inductive ty
  subgoal for R B \<sigma> \<Gamma> T1 T2
    unfolding split_beta
    by (elim disj_forward exE)
      (auto simp add: isPerm_def supp_inv_bound map_context_def[symmetric] typ_vvsubst_rrename
        typ.rrename_comps typ.FFVars_rrenames wf_eqvt extend_eqvt
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "rrename_typ \<sigma> _"])+, (rule conjI)?, rule in_context_eqvt))+
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
        apply (erule cong[OF cong[OF cong], THEN iffD1, of R, OF refl, rotated -1]) back
          apply (drule ty_fresh_extend)
          apply (simp_all add: supp_swap_bound)
          by (metis (no_types, opaque_lifting) image_iff map_context_def map_context_swap_FFVars)
      done
    done
  done

end
