theory LC
  imports
  "HOL-Library.FSet"
  "Prelim.FixedCountableVars"
  "Prelim.Swapping_vs_Permutation"
  "Binders.General_Customization"
  "Prelim.More_List"
begin

(* DATATYPE DECLARTION  *)

declare [[mrbnf_internals]]
binder_datatype 'var "Lterm" =
  Vr 'var
| Ap "'var Lterm" "'var Lterm"
| Lm x::'var t::"'var Lterm" binds x in t
for
  vvsubst: vvsubst
  tvsubst: tvsubst

(****************************)
(* DATATYPE-SPECIFIC CUSTOMIZATION  *)


(* Monomorphising: *)
instance var :: var_Lterm_pre apply standard
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)

instance var::cinf
apply standard 
  subgoal apply(rule exI[of _ "inv Variable"])
  by (simp add: bij_Variable bij_is_inj)
  subgoal using infinite_var . .

type_synonym lterm = "var Lterm"

(* Some lighter notations: *)
abbreviation "VVr \<equiv> tvVVr_tvsubst"
lemmas VVr_def = tvVVr_tvsubst_def
abbreviation "isVVr \<equiv> tvisVVr_tvsubst"
lemmas isVVr_def = tvisVVr_tvsubst_def
abbreviation "IImsupp \<equiv> IImsupp_tvsubst"
lemmas IImsupp_def = IImsupp_tvsubst_def
abbreviation "SSupp \<equiv> SSupp_tvsubst"
lemmas SSupp_def = SSupp_tvsubst_def
abbreviation "FFVars \<equiv> FFVars_Lterm"

abbreviation "rrename \<equiv> rrename_Lterm"
(* *)

lemma FFVars_tvsubst[simp]:
  assumes "|SSupp (\<sigma> :: var \<Rightarrow> lterm)| <o |UNIV :: var set|"
  shows "FFVars (tvsubst \<sigma> t) = (\<Union> {FFVars (\<sigma> x) | x . x \<in> FFVars t})"
  apply (binder_induction t avoiding: "IImsupp \<sigma>" rule: Lterm.strong_induct)
     apply (auto simp: IImsupp_def assms intro!: Un_bound UN_bound Lterm.card_of_FFVars_bounds)
  using Lterm.FVars_VVr apply (fastforce simp add: SSupp_def)
  using Lterm.FVars_VVr apply (auto simp add: SSupp_def)
  by (smt (verit) singletonD Lterm.FVars_VVr)

lemma fsupp_le[simp]: 
"fsupp (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set|" 
by (simp add: finite_card_var fsupp_def supp_def)

(* Enabling some simplification rules: *)
lemmas Lterm.tvsubst_VVr[simp] Lterm.FVars_VVr[simp]
Lterm.rrename_ids[simp] Lterm.rrename_cong_ids[simp]
Lterm.FFVars_rrenames[simp]

lemma singl_bound: "|{a}| <o |UNIV::var set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF Lterm_pre.UNIV_cinfinite]])

lemma ls_UNIV_iff_finite: "|A| <o |UNIV::var set| \<longleftrightarrow> finite A"
using finite_iff_le_card_var by blast

lemma supp_id_update_le[simp,intro]:
"|supp (id(x := y))| <o |UNIV::var set|"
by (metis finite.emptyI finite.insertI finite_card_var imsupp_id_fun_upd imsupp_supp_bound infinite_var)

lemma IImsupp_VVr_empty[simp]: "IImsupp VVr = {}"
  unfolding IImsupp_def
  Lterm.SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
  done

(* VVr is here the Vr constructor: *)
lemma VVr_eq_Vr[simp]: "VVr = Vr"
  unfolding VVr_def Vr_def comp_def
  tv\<eta>_Lterm_tvsubst_def
  by (rule refl)

(* *)
(* Properties of Lterm-for-variable substitution *)

lemma tvsubst_VVr_func[simp]: "tvsubst VVr t = t"
  apply (rule Lterm.TT_plain_co_induct)
  subgoal for x
    apply (rule case_split[of "isVVr (Lterm_ctor x)"])
     apply (unfold isVVr_def)[1]
     apply (erule exE)
    subgoal premises prems for a
      unfolding prems
      apply (rule Lterm.tvsubst_VVr)
      apply (rule Lterm.SSupp_VVr_bound)
        done
      apply (rule trans)
       apply (rule Lterm.tvsubst_cctor_not_isVVr)
          apply (rule Lterm.SSupp_VVr_bound)
      unfolding IImsupp_VVr_empty
         apply (rule Int_empty_right)
      unfolding noclash_Lterm_def Int_Un_distrib Un_empty
        apply (rule conjI)
         apply (rule iffD2[OF disjoint_iff], rule allI, rule impI, assumption)
        apply (rule iffD2[OF disjoint_iff], rule allI, rule impI)
      unfolding UN_iff Set.bex_simps
        apply (rule ballI)
        apply assumption+
      apply (rule arg_cong[of _ _ Lterm_ctor])
      apply (rule trans)
      apply (rule Lterm_pre.map_cong)
                 apply (rule supp_id_bound bij_id)+
           apply (assumption | rule refl)+
      unfolding id_def[symmetric] Lterm_pre.map_id
      apply (rule refl)
      done
    done

proposition rrename_simps[simp]:
  assumes "bij (f::var \<Rightarrow> var)" "|supp f| <o |UNIV::var set|"
  shows "rrename f (Vr a) = Vr (f a)"
    "rrename f (Ap e1 e2) = Ap (rrename f e1) (rrename f e2)"
    "rrename f (Lm x e) = Lm (f x) (rrename f e)"
  unfolding Vr_def Ap_def Lm_def Lterm.rrename_cctors[OF assms] map_Lterm_pre_def comp_def
    Abs_Lterm_pre_inverse[OF UNIV_I] map_sum_def sum.case map_prod_def prod.case id_def
    apply (rule refl)+
  done

lemma rrename_cong:
assumes "bij f" "|supp f| <o |UNIV::var set|" "bij g" "|supp g| <o |UNIV::var set|"
"(\<And>z. (z::var) \<in> FFVars P \<Longrightarrow> f z = g z)"
shows "rrename f P = rrename g P"
using assms(5) apply(binder_induction P avoiding: "supp f" "supp g" rule: Lterm.strong_induct)
using assms apply auto by (metis not_in_supp_alt)+

lemma tvsubst_cong:
assumes f: "|SSupp f| <o |UNIV::var set|" and g: "|SSupp g| <o |UNIV::var set|"
and eq: "(\<And>z. (z::var) \<in> FFVars P \<Longrightarrow> f z = g z)"
shows "tvsubst f P = tvsubst g P"
proof-
  have fg: "|IImsupp f| <o |UNIV::var set|" "|IImsupp g| <o |UNIV::var set|" 
    using f g  
    by (simp_all add: IImsupp_def Lterm.card_of_FFVars_bounds 
       Lterm_prevar_Lterm_prevar_Lterm_prevar_prodIDLterm_prevar_prodIDsum_class.UN_bound 
       Lterm_prevar_Lterm_prevar_Lterm_prevar_prodIDLterm_prevar_prodIDsum_class.Un_bound) 
  have 0: "|IImsupp f \<union> IImsupp g| <o |UNIV::var set|" 
    using fg var_Lterm_pre_class.Un_bound by blast
  show ?thesis using 0 eq apply(binder_induction P avoiding: "IImsupp f" "IImsupp g" rule: Lterm.strong_induct)
    subgoal using fg by auto
    subgoal using fg by simp  
    subgoal using f g by simp
    subgoal using f g by simp
    subgoal using f g fg apply simp unfolding IImsupp_def SSupp_def 
    by auto metis .
qed

proposition Ap_inject[simp]: "(Ap a b = Ap c d) = (a = c \<and> b = d)"
proof
  assume "Ap a b = Ap c d"
  then show "a = c \<and> b = d"
    unfolding Ap_def fun_eq_iff Lterm.TT_injects0
      map_Lterm_pre_def comp_def Abs_Lterm_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
      Abs_Lterm_pre_inject[OF UNIV_I UNIV_I]
    by blast
qed simp

proposition Vr_inject[simp]: "(Vr a = Vr b) = (a = b)"
  apply (rule iffI[rotated])
   apply (rule arg_cong[of _ _ Vr])
  apply assumption
  unfolding Vr_def Lterm.TT_injects0 map_Lterm_pre_def comp_def map_sum_def sum.case Abs_Lterm_pre_inverse[OF UNIV_I]
  id_def Abs_Lterm_pre_inject[OF UNIV_I UNIV_I] sum.inject
  apply (erule exE conjE)+
  apply assumption
  done

lemma Lm_inject: "(Lm x e = Lm x' e') = (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FFVars_Lterm (Lm x e)) f \<and> f x = x' \<and> rrename f e = e')"
  unfolding Lterm.set
  unfolding Lm_def Lterm.TT_injects0 map_Lterm_pre_def comp_def Abs_Lterm_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_Lterm_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_Lterm_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_Lterm_pre_def
    Un_empty_right UN_single
  apply (rule refl)
  done

lemma Lm_same_inject[simp]: "Lm (x::var) e = Lm x e' \<longleftrightarrow> e = e'"
unfolding Lm_inject apply safe
apply(rule Lterm.rrename_cong_ids[symmetric]) 
unfolding id_on_def by auto

lemma bij_map_Lterm_pre: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> bij (map_Lterm_pre (id::var \<Rightarrow>var) f (rrename f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_Lterm_pre id (inv f) (rrename (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule Lterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 Lterm.rrename_comp0s Lterm.rrename_id0s
  apply (rule Lterm_pre.map_id0)
  apply (rule trans)
   apply (rule Lterm_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 Lterm.rrename_comp0s Lterm.rrename_id0s
  apply (rule Lterm_pre.map_id0)
  done

lemma map_Lterm_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> inv (map_Lterm_pre (id::_::var_Lterm_pre \<Rightarrow> _) f (rrename f) id) = map_Lterm_pre id (inv f) (rrename (inv f)) id"
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
  apply assumption
  apply (rule inv_unique_comp)
   apply (rule trans)
    apply (rule Lterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
   defer
  apply (rule trans)
    apply (rule Lterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 inv_o_simp2 Lterm.rrename_comp0s Lterm.rrename_id0s Lterm_pre.map_id0
   apply (rule refl)+
  done

lemma Lm_set3: "Lterm_ctor v = Lm (x::var) e \<Longrightarrow> \<exists>x' e'. Lterm_ctor v = Lm x' e' \<and> x' \<in> set2_Lterm_pre v \<and> e' \<in> set3_Lterm_pre v"
  unfolding Lm_def Lterm.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_Lterm_pre id f (rrename f) id"])
     apply (rule bij_map_Lterm_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding Lterm.rrename_id0s Lterm_pre.map_id map_Lterm_pre_inv_simp
    unfolding map_Lterm_pre_def comp_def Abs_Lterm_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_Lterm_pre_def set3_Lterm_pre_def comp_def Abs_Lterm_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding Lterm.FFVars_rrenames[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF Lterm.rrename_bijs[OF bij_imp_bij_inv supp_inv_bound]]
  Lterm.rrename_inv_simps[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding Lterm.rrename_comps[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 Lterm.rrename_ids
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+
  done
  done

lemma Lm_avoid: "|A::var set| <o |UNIV::var set| \<Longrightarrow> \<exists>x' e'. Lm x e = Lm x' e' \<and> x' \<notin> A"
  apply (drule Lterm.TT_fresh_nchotomys[of _ "Lm x e"])
  apply (erule exE)
  apply (erule conjE)
   apply (drule sym)
  apply (frule Lm_set3)
  apply (erule exE conjE)+
  apply (rule exI)+
  apply (rule conjI)
   apply (rule trans)
    apply (rule sym)
    apply assumption
  apply (rotate_tac 2)
   apply assumption
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma Lm_rrename:
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>
 (\<And>a'. a' \<in>FFVars_Lterm e - {a::var} \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> Lm a e = Lm (\<sigma> a) (rrename \<sigma> e)"
by (metis rrename_simps(3) Lterm.rrename_cong_ids Lterm.set(3))


(* Bound properties (needed as auxiliaries): *)

lemma SSupp_upd_bound:
  fixes f::"var \<Rightarrow> lterm"
  shows "|SSupp (f (a:=t))| <o |UNIV::var set| \<longleftrightarrow> |SSupp f| <o |UNIV::var set|"
  unfolding SSupp_def
  by (auto simp only: fun_upd_apply singl_bound ordLeq_refl fset_simps split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF Lterm_pre.Un_bound], rotated, of _ "{a}"]
      intro: card_of_mono1)

corollary SSupp_upd_VVr_bound[simp,intro!]: "|SSupp (VVr(a:=(t::lterm)))| <o |UNIV::var set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule Lterm.SSupp_VVr_bound)
  done

lemma SSupp_upd_Vr_bound[simp,intro!]: "|SSupp (Vr(a:=(t::lterm)))| <o |UNIV::var set|"
using SSupp_upd_VVr_bound by auto

lemma supp_swap_bound[simp,intro!]: "|supp (id(x::var := xx, xx := x))| <o |UNIV:: var set|"
by (simp add: cinfinite_imp_infinite supp_swap_bound Lterm.UNIV_cinfinite)

lemma SSupp_IImsupp_bound: "|SSupp \<sigma>| <o |UNIV:: var set| \<Longrightarrow> |IImsupp \<sigma>| <o |UNIV:: var set|"
unfolding IImsupp_def
by (simp add: var_ID_class.Un_bound Lterm.set_bd_UNIV var_Lterm_pre_class.UN_bound)

(* *)

lemma IImsupp_tvsubst_su:
assumes s[simp]: "|SSupp \<sigma>| <o  |UNIV:: var set|"
shows "IImsupp (tvsubst (\<sigma>::var\<Rightarrow>lterm) o \<tau>) \<subseteq> IImsupp \<sigma> \<union> IImsupp \<tau>"
unfolding IImsupp_def SSupp_def apply auto
by (metis s singletonD Lterm.set(1) Lterm.subst(1))

lemma IImsupp_tvsubst_su':
assumes s[simp]: "|SSupp \<sigma>| <o  |UNIV:: var set|"
shows "IImsupp (\<lambda>a. tvsubst (\<sigma>::var\<Rightarrow>lterm) (\<tau> a)) \<subseteq> IImsupp \<sigma> \<union> IImsupp \<tau>"
using IImsupp_tvsubst_su[OF assms] unfolding o_def .

lemma IImsupp_tvsubst_bound:
assumes s: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|IImsupp (tvsubst (\<sigma>::var\<Rightarrow>lterm) o \<tau>)| <o |UNIV:: var set|"
using IImsupp_tvsubst_su[OF s(1)] s
by (meson Un_bound SSupp_IImsupp_bound card_of_subset_bound)

lemma SSupp_tvsubst_bound:
assumes s: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|SSupp (tvsubst (\<sigma>::var\<Rightarrow>lterm) o \<tau>)| <o |UNIV:: var set|"
using IImsupp_tvsubst_bound[OF assms]
by (metis IImsupp_def card_of_subset_bound sup_ge1)

lemma SSupp_tvsubst_bound':
assumes s: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|SSupp (\<lambda>a. tvsubst (\<sigma>::var\<Rightarrow>lterm) (\<tau> a))| <o |UNIV:: var set|"
using SSupp_tvsubst_bound[OF assms] unfolding o_def .

(* *)

lemma IImsupp_Vr: "IImsupp (Vr(x := e)) \<subseteq> FFVars e \<union> {x}"
unfolding LC.IImsupp_def LC.SSupp_def by auto

lemma IImsupp_Vr': "y \<noteq> x \<and> y \<notin> FFVars e \<Longrightarrow> y \<notin> IImsupp (Vr(x := e))"
using IImsupp_Vr by auto 

lemma IImsupp_rrename_su:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|"
shows "IImsupp (rrename (\<sigma>::var\<Rightarrow>var) o \<tau>) \<subseteq> imsupp \<sigma> \<union> IImsupp \<tau>"
unfolding IImsupp_def imsupp_def supp_def SSupp_def by force

lemma IImsupp_rrename_su':
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|"
shows "IImsupp (\<lambda>a. rrename (\<sigma>::var\<Rightarrow>var) (\<tau> a)) \<subseteq> imsupp \<sigma> \<union> IImsupp \<tau>"
using IImsupp_rrename_su[OF assms] unfolding o_def .

lemma IImsupp_rrename_bound:
assumes s: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|IImsupp (rrename (\<sigma>::var\<Rightarrow>var) o \<tau>)| <o |UNIV:: var set|"
using IImsupp_rrename_su[OF s(1,2)] s
by (metis SSupp_IImsupp_bound finite_Un finite_iff_le_card_var finite_subset imsupp_supp_bound infinite_var)

lemma SSupp_rrename_bound:
assumes s: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|SSupp (rrename (\<sigma>::var\<Rightarrow>var) o \<tau>)| <o |UNIV:: var set|"
using IImsupp_rrename_bound[OF assms]
by (metis IImsupp_def card_of_subset_bound sup_ge1)

lemma SSupp_rrename_bound':
assumes s: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|SSupp (\<lambda>a. rrename (\<sigma>::var\<Rightarrow>var) (\<tau> a))| <o |UNIV:: var set|"
using SSupp_rrename_bound[OF assms] unfolding o_def .

(* *)
lemma SSupp_update_rrename_bound:
"|SSupp (Vr(\<sigma> (x::var) := rrename \<sigma> e))| <o |UNIV::var set|"
using SSupp_upd_Vr_bound .

lemma IImsupp_rrename_update_su:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "IImsupp (rrename \<sigma> \<circ> Vr(x := e)) \<subseteq>
       imsupp \<sigma> \<union> {x} \<union> FFVars_Lterm e"
unfolding IImsupp_def SSupp_def imsupp_def supp_def by (auto split: if_splits)

lemma IImsupp_rrename_update_bound:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "|IImsupp (rrename \<sigma> \<circ> Vr(x := e))| <o |UNIV::var set|"
using IImsupp_rrename_update_su[OF assms]
by (meson Un_bound card_of_subset_bound imsupp_supp_bound infinite_var s(2) singl_bound Lterm.set_bd_UNIV)

lemma SSupp_rrename_update_bound:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "|SSupp (rrename \<sigma> \<circ> Vr(x := e))| <o |UNIV::var set|"
using IImsupp_rrename_update_bound[OF assms]
  by (metis (mono_tags) IImsupp_def finite_Un finite_iff_le_card_var)

(* Action of swapping (a particular renaming) on variables *)

lemma rrename_swap_Vr1[simp]: "rrename (id(x := xx, xx := x)) (Vr (x::var)) = Vr xx"
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Vr2[simp]: "rrename (id(x := xx, xx := x)) (Vr (xx::var)) = Vr x"
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Vr3[simp]: "z \<notin> {x,xx} \<Longrightarrow> rrename (id(x := xx, xx := x)) (Vr (z::var)) = Vr z"
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Vr[simp]: "rrename (id(x := xx, xx := x)) (Vr (z::var)) =
 Vr (if z = x then xx else if z = xx then x else z)"
apply(subst rrename_simps(1)) by auto

(* Compositionality properties of renaming and Lterm-for-variable substitution *)

lemma tvsubst_comp:
assumes s[simp]: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "tvsubst (\<sigma>::var\<Rightarrow>lterm) (tvsubst \<tau> e) = tvsubst (tvsubst \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_tvsubst_bound'[OF s, simp]
  show ?thesis
  apply(induct e rule: Lterm.fresh_induct[where A = "IImsupp \<sigma> \<union> IImsupp \<tau>"])
    subgoal using Un_bound[OF s]
      using var_ID_class.Un_bound SSupp_IImsupp_bound s(1) s(2) by blast
    subgoal by simp
    subgoal by simp
    subgoal for x t apply(subgoal_tac "x \<notin> IImsupp (\<lambda>a. tvsubst \<sigma> (\<tau> a))")
      subgoal by simp
      subgoal using IImsupp_tvsubst_su'[OF s(1)] by blast . .
qed

lemma rrename_tvsubst_comp:
assumes b[simp]: "bij (\<sigma>::var\<Rightarrow>var)" and s[simp]: "|supp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "rrename \<sigma> (tvsubst \<tau> e) = tvsubst (rrename \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_rrename_bound'[OF b s, simp]
  show ?thesis
  apply(induct e rule: Lterm.fresh_induct[where A = "IImsupp \<tau> \<union> imsupp \<sigma>"])
    subgoal using s(1) s(2) Un_bound SSupp_IImsupp_bound imsupp_supp_bound infinite_var by blast
    subgoal by simp
    subgoal by simp
    subgoal for x t apply simp apply(subgoal_tac "x \<notin> IImsupp (\<lambda>a. rrename  \<sigma> (\<tau> a))")
      subgoal unfolding imsupp_def supp_def by simp
      subgoal using IImsupp_rrename_su' b s(1) by blast . .
qed


(* Unary (Lterm-for-var) substitution versus renaming: *)

lemma supp_SSupp_Vr_le[simp]: "SSupp (Vr \<circ> \<sigma>) = supp \<sigma>" 
unfolding supp_def SSupp_def by simp

lemma rrename_eq_tvsubst_Vr: 
assumes "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|" 
shows "rrename \<sigma> = tvsubst (Vr o \<sigma>)"
proof
  fix t
  show "rrename \<sigma> t = tvsubst (Vr o \<sigma>) t"
  proof (binder_induction t avoiding: "IImsupp (Vr \<circ> \<sigma>)" rule: Lterm.strong_induct)
    case Bound
    then show ?case using assms SSupp_IImsupp_bound by (metis supp_SSupp_Vr_le)
  next
    case (Lm x1 x2)
    then show ?case by (simp add: assms IImsupp_def disjoint_iff not_in_supp_alt)
  qed (auto simp: assms)
qed
     
lemma rrename_eq_tvsubst_Vr': 
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> rrename \<sigma> e = tvsubst (Vr o \<sigma>) e"
using rrename_eq_tvsubst_Vr by auto

(* Equivariance of unary substitution: *)

lemma tvsubst_rrename_comp[simp]:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "tvsubst (rrename \<sigma> \<circ> Vr(x := e2)) e1 = tvsubst (Vr(\<sigma> x := rrename \<sigma> e2)) (rrename \<sigma> e1)"
proof-
  note SSupp_rrename_update_bound[OF assms, unfolded comp_def, simplified, simp]
  note SSupp_update_rrename_bound[unfolded fun_upd_def, simplified, simp]
  show ?thesis
  apply(induct e1 rule: Lterm.fresh_induct[where A = "{x} \<union> FFVars_Lterm e2 \<union> imsupp \<sigma>"])
    subgoal by (meson Un_bound imsupp_supp_bound infinite_var s(2) singl_bound Lterm.set_bd_UNIV)
    subgoal by auto
    subgoal by simp
    subgoal for y t apply simp apply(subgoal_tac
      "y \<notin> IImsupp ((\<lambda>a. rrename \<sigma> (if a = x then e2 else Vr a))) \<and>
      \<sigma> y \<notin> IImsupp (\<lambda>a. if a = \<sigma> x then rrename \<sigma> e2 else Vr a)")
      subgoal unfolding imsupp_def supp_def by simp
      subgoal unfolding IImsupp_def imsupp_def SSupp_def supp_def by auto . .
qed

(* Unary substitution versus swapping: *)
lemma tvsubst_refresh:
assumes xx: "xx \<notin> FFVars_Lterm e1 - {x}"
shows "tvsubst (Vr((x::var) := e2)) e1 = tvsubst (Vr(xx := e2)) (rrename (id(x := xx, xx := x)) e1)"
proof-
  show ?thesis using xx
  apply(induct e1 rule: Lterm.fresh_induct[where A = "{x,xx} \<union> FFVars_Lterm e2"])
    subgoal by (metis insert_is_Un Lterm.set(1) Lterm.set(2) Lterm.set_bd_UNIV)
    subgoal by simp
    subgoal by auto
    subgoal for y t apply simp apply(subgoal_tac
      "y \<notin> IImsupp (Vr(x := e2)) \<and> y \<notin> IImsupp (Vr(xx := e2))")
      subgoal unfolding imsupp_def supp_def by auto
      subgoal unfolding IImsupp_def imsupp_def SSupp_def supp_def by auto . .
qed

(*   *)

(* *)

(* Swapping and unary substitution, as abbreviations: *)
abbreviation "swap t (x::var) y \<equiv> rrename (id(x:=y,y:=x)) t"
abbreviation "usub t (y::var) x \<equiv> vvsubst (id(x:=y)) t"

(* *)

lemma usub_swap_disj:
assumes "{u,v} \<inter> {x,y} = {}"
shows "usub (swap t u v) x y = swap (usub t x y) u v"
proof-
  note Lterm_vvsubst_rrename[simp del]
  show ?thesis using assms
  apply(subst Lterm_vvsubst_rrename[symmetric]) apply auto
  apply(subst Lterm.map_comp) apply auto
  apply(subst Lterm_vvsubst_rrename[symmetric]) apply auto
  apply(subst Lterm.map_comp) apply auto
  apply(rule Lterm.map_cong0)
    using Lterm_pre.supp_comp_bound by auto
qed

lemma rrename_o_swap:
"rrename (id(y::var := yy, yy := y) o id(x := xx, xx := x)) t =
 swap (swap t x xx) y yy"
apply(subst Lterm.rrename_comps[symmetric])
by auto

(* *)

lemma swap_simps[simp]: "swap (Vr z) (y::var) x = Vr (sw z y x)"
"swap (Ap t s) (y::var) x = Ap(swap t y x) (swap s y x)"
"swap (Lm v t) (y::var) x = Lm (sw v y x) (swap t y x)"
by (auto simp: sw_def)

lemma FFVars_swap[simp]: "FFVars (swap t y x) =
 (\<lambda>u. sw u x y) ` (FFVars t)"
apply(subst Lterm.FFVars_rrenames) by (auto simp: sw_def)

lemma FFVars_swap'[simp]: "{x::var,y} \<inter> FFVars t = {} \<Longrightarrow> swap t x y = t"
apply(rule Lterm.rrename_cong_ids) by auto

(* *)

lemma Lm_inject_swap: "Lm v t = Lm v' t' \<longleftrightarrow>
  (v' \<notin> FFVars t \<or> v' = v) \<and> swap t v' v = t'"
unfolding Lm_inject apply(rule iffI)
  subgoal unfolding id_on_def apply auto
  apply(rule rrename_cong) by auto
  subgoal apply clarsimp
  apply(rule exI[of _ "id(v':=v,v:=v')"]) unfolding id_on_def by auto .

lemma Lm_inject_swap': "Lm v t = Lm v' t' \<longleftrightarrow>
  (\<exists>z. (z \<notin> FFVars t \<or> z = v) \<and> (z \<notin> FFVars t' \<or> z = v') \<and>
       swap t z v = swap t' z v')"
unfolding Lm_inject_swap apply(rule iffI)
  subgoal apply clarsimp apply(rule exI[of _ v']) by auto
  subgoal by (smt (verit, del_insts) Lm_inject_swap)    .

lemma Lm_refresh': "v' \<notin> FFVars t \<or> v' = v \<Longrightarrow>
   Lm v t = Lm v' (swap t v' v)"
using Lm_inject_swap by auto

lemma Lm_refresh:
"xx \<notin> FFVars t \<or> xx = x \<Longrightarrow> Lm x t = Lm xx (swap t x xx)"
by (metis Lm_inject_swap fun_upd_twist)

(* *)

lemma FFVars_usub[simp]: "FFVars (usub t y x) =
 (if x \<in> FFVars t then FFVars t - {x} \<union> {y} else FFVars t)"
apply(subst Lterm.set_map) by auto

lemma usub_simps_free[simp]: "\<And>y x. usub (Vr z) (y::var) x = Vr (sb z y x)"
"\<And>y x t s. usub (Ap t s) (y::var) x = Ap (usub t y x) (usub s y x)"
by (auto simp: sb_def)

lemma usub_Lm[simp]:
"v \<notin> {x,y} \<Longrightarrow> usub (Lm v t) (y::var) x = Lm v (usub t y x)"
apply(subst Lterm.map)
  subgoal by auto
  subgoal by (auto simp: imsupp_def supp_def)
  subgoal by auto .

lemmas usub_simps = usub_simps_free usub_Lm

(* *)

lemma rrename_usub[simp]:
assumes \<sigma>: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
shows "rrename \<sigma> (usub t u (x::var)) = usub (rrename \<sigma> t) (\<sigma> u) (\<sigma> x)"
using assms
apply(binder_induction t avoiding: "supp \<sigma>" u x rule: Lterm.strong_induct)
using assms by (auto simp: sb_def)

lemma sw_sb:
"sw (sb z u x) z1 z2 = sb (sw z z1 z2) (sw u z1 z2) (sw x z1 z2)"
unfolding sb_def sw_def by auto


lemma swap_usub:
"swap (usub t (u::var) x) z1 z2 = usub (swap t z1 z2) (sw u z1 z2) (sw x z1 z2)"
apply(binder_induction t avoiding: u x z1 z2 rule: Lterm.strong_induct)
  subgoal
  apply(subst swap_simps) apply(subst usub_simps) by (auto simp: sb_def)
  subgoal apply(subst swap_simps | subst usub_simps)+ by presburger
  subgoal apply(subst swap_simps | subst usub_simps)+
    subgoal by auto
    subgoal apply(subst swap_simps | subst usub_simps)+
      subgoal unfolding sw_def sb_def by auto
      unfolding sw_sb by presburger . .

lemma usub_refresh:
assumes "xx \<notin> FFVars t \<or> xx = x"
shows "usub t u x = usub (swap t x xx) u xx"
proof-
  note Lterm_vvsubst_rrename[simp del]
  show ?thesis using assms
  apply(subst Lterm_vvsubst_rrename[symmetric]) apply simp
    subgoal by auto
    subgoal apply(subst Lterm.map_comp)
      subgoal by auto
      subgoal by auto
      subgoal apply(rule Lterm.map_cong0)
      using Lterm_pre.supp_comp_bound by auto . .
qed

lemma swap_commute:
"{y,yy} \<inter> {x,xx} = {} \<Longrightarrow>
 swap (swap t y yy) x xx = swap (swap t x xx) y yy"
apply(subst Lterm.rrename_comps)
apply auto
apply(subst Lterm.rrename_comps)
apply auto
apply(rule rrename_cong)
by (auto simp: Lterm_pre.supp_comp_bound)


(* *)

lemma swappingFvars_swap_FFVars: "swappingFvars swap FFVars"
unfolding swappingFvars_def apply auto
  apply (metis id_swapTwice rrename_o_swap Lterm.rrename_ids) 
  using sw_invol2 apply metis 
  by (metis (no_types, lifting) image_iff sw_invol2)

lemma nswapping_swap: "nswapping swap"
unfolding nswapping_def apply auto
apply (metis id_swapTwice rrename_o_swap Lterm.rrename_ids)
by (metis id_swapTwice2 rrename_o_swap)

lemma permutFvars_rrename_FFVr: "permutFvars (\<lambda>t f. rrename f (t::lterm)) FFVars"
unfolding permutFvars_def apply auto
  apply (simp add: finite_iff_le_card_var fsupp_def supp_def Lterm.rrename_comps) 
  apply (simp add: finite_iff_le_card_var fsupp_def supp_def)
  apply (simp add: finite_iff_le_card_var fsupp_def image_in_bij_eq supp_def) .

lemma permut_rrename: "permut (\<lambda>t f. rrename f (t::lterm))"
unfolding permut_def apply auto
by (simp add: finite_iff_le_card_var fsupp_def supp_def Lterm.rrename_comps)

lemma toSwp_rrename: "toSwp (\<lambda>t f. rrename f t) = swap"
by (meson toSwp_def)

lemma fsupp_supp: "fsupp f \<longleftrightarrow> |supp f| <o |UNIV::var set|"
unfolding fsupp_def supp_def using finite_iff_le_card_var by blast

lemma toPerm_swap: "bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow> toPerm swap t f = rrename f t"
apply(subst toSwp_rrename[symmetric])
by (simp add: fsupp_supp permut_rrename toPerm_toSwp)


(* *)
(* Substitution from a sequence (here, a list) *)

(* "making" the substitution function that maps each xs_i to es_i; only 
meaningful if xs is non-repetitive *)
definition "mkSubst xs es \<equiv> \<lambda>x. if distinct xs \<and> x \<in> set xs then nth es (theN xs x) else Vr x"

lemma mkSubst_nth[simp]: "distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> mkSubst xs es (nth xs i) = nth es i"
unfolding mkSubst_def by auto

lemma mkSubst_idle[simp]: "\<not> distinct xs \<or> \<not> x \<in> set xs \<Longrightarrow> mkSubst xs es x = Vr x"
unfolding mkSubst_def by auto

lemma card_set_var: "|set xs| <o |UNIV::var set|"
by (simp add: infinite_var) 

lemma SSupp_mkSubst[simp,intro]: "|SSupp (mkSubst xs es)| <o |UNIV::var set|"
proof-
  have "SSupp (mkSubst xs es) \<subseteq> set xs"
  unfolding SSupp_def by auto (metis mkSubst_idle)
  thus ?thesis by (simp add: card_of_subset_bound card_set_var)
qed

lemma mkSubst_map_rrename: 
assumes s: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|" 
and l: "length es2 = length xs"
shows "mkSubst (map \<sigma> xs) (map (rrename \<sigma>) es2) \<circ> \<sigma> = rrename \<sigma> \<circ> mkSubst xs es2"
proof(rule ext)  
  fix x
  show "(mkSubst (map \<sigma> xs) (map (rrename \<sigma>) es2) \<circ> \<sigma>) x = (rrename \<sigma> \<circ> mkSubst xs es2) x"
  proof(cases "distinct xs \<and> x \<in> set xs")
    case False
    hence F: "\<not> distinct (map \<sigma> xs) \<or> \<not> \<sigma> x \<in> set (map \<sigma> xs)"
    using s by auto
    thus ?thesis using F False
    unfolding o_def apply(subst mkSubst_idle) 
      subgoal by auto
      subgoal using s by auto .
  next
    case True
    then obtain i where i: "i < length xs" and Tr: "distinct xs" and Tri: "x = nth xs i" by (metis theN)
    hence T: "distinct (map \<sigma> xs)" and Ti: "\<sigma> x = nth (map \<sigma> xs) i"
    using s by auto
    thus ?thesis using T Tr
    unfolding o_def Ti apply(subst mkSubst_nth) 
      subgoal by auto
      subgoal using i unfolding Tri by auto 
      subgoal using l i unfolding Tri by auto .
  qed
qed

lemma mkSubst_map_rrename_inv: 
assumes "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|" "length es2 = length xs"
shows "mkSubst (map \<sigma> xs) (map (rrename \<sigma>) es2) = rrename \<sigma> \<circ> mkSubst xs es2 o inv \<sigma>"
unfolding mkSubst_map_rrename[OF assms, symmetric] using assms unfolding fun_eq_iff by auto

lemma card_SSupp_itvsubst_mkSubst_rrename_inv: 
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
 length es = length xs \<Longrightarrow> 
|SSupp (tvsubst (rrename \<sigma> \<circ> mkSubst xs es \<circ> inv \<sigma>) \<circ> (Vr \<circ> \<sigma>))| <o |UNIV::var set|"
by (metis SSupp_tvsubst_bound SSupp_mkSubst mkSubst_map_rrename_inv supp_SSupp_Vr_le)

lemma card_SSupp_mkSubst_rrename_inv: 
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
 length es = length xs \<Longrightarrow> 
 |SSupp (rrename \<sigma> \<circ> mkSubst xs es \<circ> inv \<sigma>)| <o |UNIV::var set|"
by (metis SSupp_mkSubst mkSubst_map_rrename_inv)

lemma mkSubst_smap: "bij f \<Longrightarrow> distinct xs \<Longrightarrow> z \<in> set xs \<Longrightarrow> 
 length es = length xs \<Longrightarrow> 
 mkSubst (map f xs) es (f z) = mkSubst xs es z"
by (metis bij_distinct_smap distinct_Ex1 length_map mkSubst_nth nth_map) 


(* *)

lemma Lm_eq_tvsubst: 
assumes il: "Lm (x::var) e1 = Lm x' e1'"
shows "tvsubst (Vr (x:=e2)) e1 = tvsubst (Vr (x':=e2)) e1'"
proof-
  obtain f where f: "bij f" "|supp f| <o |UNIV::var set|" "id_on (FFVars (Lm x e1)) f" 
  and 0: "x' = f x" "e1' = rrename f e1" using il[unfolded Lm_inject] by auto
  show ?thesis unfolding 0 apply(subst rrename_eq_tvsubst_Vr')
    subgoal by fact subgoal by fact
    subgoal apply(subst tvsubst_comp)
      subgoal by simp
      subgoal using f(2) by auto
      subgoal apply(rule tvsubst_cong)
        subgoal by simp
        subgoal by (simp add: SSupp_tvsubst_bound f(2))
        subgoal apply simp 
     subgoal using f(1) f(3) id_onD by fastforce . . . .
qed




(* RECURSOR PREPARATIONS: *)

thm Lm_inject[no_vars]

lemma Lm_inject_strong:
assumes "Lm (x::var) e = Lm x' e'"
shows "\<exists>f. bij f \<and> |supp f| <o |UNIV::var set| \<and>  
   id_on (- {x,x'}) f \<and> id_on (FFVars (Lm x e)) f \<and>
   f x = x' \<and> rrename f e = e'" 
apply(rule exI[of _ "id(x := x', x' := x)"])
using assms unfolding Lm_inject_swap apply safe
unfolding id_on_def by auto (metis fun_upd_twist)


lemma Lm_inject_strong':
assumes il: "Lm (x::var) e = Lm x' e'" and z: "z \<notin> FFVars (Lm x e) \<union> FFVars (Lm x' e')"
shows 
"\<exists>f f'. 
   bij f \<and> |supp f| <o |UNIV::var set| \<and> id_on (- {x,z}) f \<and> id_on (FFVars (Lm x e)) f \<and> f x = z \<and> 
   bij f' \<and> |supp f'| <o |UNIV::var set| \<and> id_on (- {x',z}) f' \<and> id_on (FFVars (Lm x' e')) f' \<and> f' x' = z \<and> 
   rrename f e = rrename f' e'"
proof-
  define f where "f = id(x := z, z := x)"
  have f: "bij f \<and> |supp f| <o |UNIV::var set| \<and> id_on (- {x,z}) f \<and> id_on (FFVars (Lm x e)) f \<and> f x = z"
  using z unfolding f_def id_on_def by auto
  define f' where "f' = id(x' := z, z := x')"
  have f': "bij f' \<and> |supp f'| <o |UNIV::var set| \<and> id_on (- {x',z}) f' \<and> id_on (FFVars (Lm x' e')) f' \<and> f' x' = z"
  using z unfolding f'_def id_on_def by auto
 
  obtain g where g: "bij g \<and> |supp g| <o |UNIV::var set| \<and> id_on (FFVars (Lm x e)) g \<and> g x = x'" and ge: "e' = rrename g e"
  using il unfolding Lm_inject by auto

  have ff': "rrename f e = rrename f' e'" 
  unfolding f_def f'_def ge unfolding f_def f'_def using g apply(subst Lterm.rrename_comps)
    subgoal by auto  subgoal by auto subgoal by auto subgoal by auto
    subgoal apply(rule rrename_cong) using g
      subgoal by auto  subgoal by auto subgoal by auto 
      subgoal using Lterm_pre.supp_comp_bound by auto
      subgoal using Lterm_pre.supp_comp_bound z unfolding id_on_def by auto . .

  show ?thesis
  apply(rule exI[of _ f]) apply(rule exI[of _ f'])
  using f f' ff' by auto
qed

lemma lterm_rrename_induct[case_names Vr Ap Lm]:
assumes VVr: "\<And>x. P (Vr (x::var))"
and AAp: "\<And>e1 e2. P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (Ap e1 e2)" 
and LLm: "\<And>x e. (\<And>f. bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow> P (rrename f e)) \<Longrightarrow> P (Lm x e)"
shows "P t"
proof-
  have "\<forall>f. bij f \<and> |supp f| <o |UNIV::var set| \<longrightarrow> P (rrename f t)"
  proof(induct)
    case (Vr x)
    then show ?case using VVr by auto
  next
    case (Ap t1 t2)
    then show ?case using AAp by auto
  next
    case (Lm x t)
    then show ?case using LLm
      by simp (metis bij_o Lterm.rrename_comps Lterm_pre.supp_comp_bound)
  qed
  thus ?thesis apply(elim allE[of _ id]) by auto
qed

(* RECURSOR *)

locale LC_Rec = 
fixes B :: "'b set"
and VrB :: "var \<Rightarrow> 'b" 
and ApB :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
and LmB :: "var \<Rightarrow> 'b \<Rightarrow> 'b"
and renB :: "(var \<Rightarrow> var) \<Rightarrow> 'b \<Rightarrow> 'b"
and FVarsB :: "'b \<Rightarrow> var set"
assumes 
(* closedness: *)
VrB_B[simp,intro]: "\<And>x. VrB x \<in> B"
and 
ApB_B[simp,intro]: "\<And>b1 b2. {b1,b2} \<subseteq> B \<Longrightarrow> ApB b1 b2 \<in> B"
and 
LmB_B[simp,intro]: "\<And>x b. b \<in>  B \<Longrightarrow> LmB x b \<in> B"
and 
renB_B[simp]: "\<And>\<sigma> b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> renB \<sigma> b \<in> B"
and 
(* proper axioms: *)
renB_id[simp,intro]: "\<And>b. b \<in> B \<Longrightarrow> renB id b = b"
and 
renB_comp[simp,intro]: "\<And>b \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
    bij \<tau> \<Longrightarrow> |supp \<tau>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> renB (\<tau> o \<sigma>) b = renB \<tau> (renB \<sigma> b)"
and 
renB_cong[simp]: "\<And>\<sigma> b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
   (\<forall>x \<in> FVarsB b. \<sigma> x = x) \<Longrightarrow> 
   renB \<sigma> b = b"
(* and 
NB: This is redundant:  
renB_FVarsB[simp]: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b"
*)
and 
(* *)
renB_VrB[simp]: "\<And>\<sigma> x. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> renB \<sigma> (VrB x) = VrB (\<sigma> x)"
and 
renB_ApB[simp]: "\<And>\<sigma> b1 b2. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> {b1,b2} \<subseteq> B \<Longrightarrow> 
   renB \<sigma> (ApB b1 b2) = ApB (renB \<sigma> b1) (renB \<sigma> b2)"
and 
renB_LmB[simp]: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> 
   renB \<sigma> (LmB x b) = LmB (\<sigma> x) (renB \<sigma> b)"
(* *)
and 
FVarsB_VrB: "\<And>x. FVarsB (VrB x) \<subseteq> {x}"
and 
FVarsB_ApB: "\<And>b1 b2. {b1,b2} \<subseteq> B \<Longrightarrow> FVarsB (ApB b1 b2) \<subseteq> FVarsB b1 \<union> FVarsB b2"
and 
FVarsB_LmB: "\<And>x b. b \<in> B \<Longrightarrow> FVarsB (LmB x b) \<subseteq> FVarsB b - {x}"
begin 

lemma not_in_FVarsB_LmB: "b \<in> B \<Longrightarrow> x \<notin> FVarsB (LmB x b)"
using FVarsB_LmB by auto

lemma LmB_inject_strong_rev: 
assumes bb': "{b,b'} \<subseteq> B" and 
x': "x' = x \<or> x' \<notin> FVarsB b" and 
f: "bij f" "|supp f| <o |UNIV::var set|" 
"id_on (- {x, x'}) f" "f x = x'" and r: "renB f b = b'"
shows "LmB x b = LmB x' b'"
proof-
  have id: "id_on (FVarsB (LmB x b)) f"
  using f FVarsB_LmB bb' x' unfolding id_on_def by auto
  have "LmB x b = renB f (LmB x b)"
  apply(rule sym) apply(rule renB_cong) using f bb' FVarsB_LmB unfolding id_on_def 
  using id unfolding id_on_def by auto
  also have "\<dots> = LmB x' b'" apply(subst renB_LmB) using f r bb' by auto
  finally show ?thesis .
qed

lemma LmB_inject_strong'_rev: 
assumes bb': "{b,b'} \<subseteq> B"  
and z: "z = x \<or> z \<notin> FVarsB b" "z = x' \<or> z \<notin> FVarsB b'"
and f: "bij f" "|supp f| <o |UNIV::var set|" "id_on (- {x, z}) f" "f x = z" 
and f': "bij f'" "|supp f'| <o |UNIV::var set|" "id_on (- {x', z}) f'" "f' x' = z" 
and r: "renB f b = renB f' b'"
shows "LmB x b = LmB x' b'" 
proof-
  define c where c: "c = renB f b"
  have c': "c = renB f' b'" unfolding c r ..
  have "LmB x b = LmB z c"  
  apply(rule LmB_inject_strong_rev[of _ _ _ _ f]) 
  using assms FVarsB_LmB id_on_def unfolding c by auto
  also have "LmB z c = LmB x' b'"  
  apply(rule sym, rule LmB_inject_strong_rev[of _ _ _ _ f']) 
  using assms FVarsB_LmB id_on_def unfolding c by auto
  finally show ?thesis .
qed

(* NB: 
We obtain a more general recursor if we replace renB_cong with LmB_inject_strong_rev; 
and an even more general one if we replace it with LmB_inject_strong'_rev. 
*)

definition morFromTrm where 
"morFromTrm H \<equiv> 
 (\<forall>e. H e \<in> B) \<and>  
 (\<forall>x. H (Vr x) = VrB x) \<and> 
 (\<forall>e1 e2. H (Ap e1 e2) = ApB (H e1) (H e2)) \<and> 
 (\<forall>x e. H (Lm x e) = LmB x (H e)) \<and> 
 (\<forall>\<sigma> e. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<longrightarrow> H (rrename \<sigma> e) = renB \<sigma> (H e)) \<and> 
 (\<forall>e. FVarsB (H e) \<subseteq> FFVars e)"

(* *)

inductive R where 
Vr: "R (Vr x) (VrB x)"
|
Ap: "R e1 b1 \<Longrightarrow> R e2 b2 \<Longrightarrow> R (Ap e1 e2) (ApB b1 b2)"
|
Lm: "R e b \<Longrightarrow> R (Lm x e) (LmB x b)"

(* *)

lemma R_Vr_elim[simp]: "R (Vr x) b \<longleftrightarrow> b = VrB x"
apply safe
  subgoal using R.cases by fastforce
  subgoal by (auto intro: R.intros) .

lemma R_Ap_elim: 
assumes "R (Ap e1 e2) b"
shows "\<exists>b1 b2. R e1 b1 \<and> R e2 b2 \<and> b = ApB b1 b2"
by (metis Ap_inject R.simps assms Lterm.distinct(1) Lterm.distinct(4))

lemma R_Lm_elim: 
assumes "R (Lm x e) b"
shows "\<exists>x' e' b'. R e' b' \<and> Lm x e = Lm x' e' \<and> b = LmB x' b'"
using assms by (cases rule: R.cases) auto

lemma R_total: 
"\<exists>b. R e b"
apply(induct e) by (auto intro: R.intros)

lemma R_B: 
"R e b \<Longrightarrow> b \<in> B"
apply(induct rule: R.induct) by auto

lemma R_main: 
"(\<forall>b b'. R e b \<longrightarrow> R e b' \<longrightarrow> b = b') \<and> 
 (\<forall>b. R e b \<longrightarrow> FVarsB b \<subseteq> FFVars e) \<and> 
 (\<forall>b f. R e b \<and> bij f \<and> |supp f| <o |UNIV::var set|
        \<longrightarrow> R (rrename f e) (renB f b))"
proof(induct e rule: lterm_rrename_induct)
  case (Vr x)
  then show ?case using FVarsB_VrB by auto
next
  case (Ap e1 e2)
  then show ?case apply safe 
    subgoal by (metis R_Ap_elim)
    subgoal by simp (smt (verit, del_insts) FVarsB_ApB R_Ap_elim 
      R_B Un_iff bot.extremum insert_Diff insert_subset)
    subgoal apply(drule R_Ap_elim) 
      by (smt (verit, del_insts) R.simps R_B bot.extremum insert_subset renB_ApB 
      rrename_simps(2)) .
next
  case (Lm x t)
  note Lmm = Lm[rule_format]
  note Lm1 = Lmm[THEN conjunct1, rule_format]
  note Lm2 = Lmm[THEN conjunct2, THEN conjunct1, rule_format]
  note Lm3 = Lmm[THEN conjunct2, THEN conjunct2, rule_format, OF _ _ conjI, OF _ _ _ conjI]
  note Lm33 = Lm3[of id, simplified]

  show ?case proof safe
    fix b1 b2 assume RLm: "R (Lm x t) b1" "R (Lm x t) b2" 
    then obtain x1' t1' b1' x2' t2' b2'
    where 1: "R t1' b1'" "Lm x t = Lm x1' t1'" "b1 = LmB x1' b1'"
    and   2: "R t2' b2'" "Lm x t = Lm x2' t2'" "b2 = LmB x2' b2'"
    using R_Lm_elim by metis

    have b12': "{b1',b2'} \<subseteq> B"
    using 1(1,3) 2(1,3) R_B by auto

    have "|{x,x1',x2'} \<union> FFVars t \<union> FFVars t1' \<union> FFVars t2'| <o |UNIV::var set|"
    by (metis Un_insert_right singl_bound sup_bot_right Lterm.set_bd_UNIV var_Lterm_pre_class.Un_bound)
    then obtain z where z: 
    "z \<notin> {x,x1',x2'} \<union> FFVars t \<union> FFVars t1' \<union> FFVars t2'" 
    by (meson exists_fresh)

    obtain f1 f1' where 
    f1: "bij f1" "|supp f1| <o |UNIV::var set|"
       "id_on (- {x, z}) f1 \<and> id_on (FFVars (Lm x t)) f1" and 
    f1': "bij f1'" "|supp f1'| <o |UNIV::var set|"
       "id_on (- {x1', z}) f1' \<and> id_on (FFVars (Lm x1' t1')) f1'"
    and z1: "f1 x = z" "f1' x1' = z"  
    and f1f1': "rrename f1 t = rrename f1' t1'"   
    using z Lm_inject_strong'[OF 1(2), of z] by auto

    have if1': "bij (inv f1' o f1)" "|supp (inv f1' o f1)| <o |UNIV::var set|"
    by (auto simp add: f1 f1' Lterm_pre.supp_comp_bound)

    have t1': "t1' = rrename (inv f1' o f1) t"  
    using f1f1' by (metis (mono_tags, lifting) bij_imp_bij_inv f1 f1' 
       inv_o_simp1 supp_inv_bound Lterm.rrename_comps Lterm.rrename_ids)

    have fvb1': "FVarsB b1' \<subseteq> FFVars t1'"
    using Lm2[OF if1', unfolded t1'[symmetric], OF 1(1)] .

    obtain f2 f2' where 
    f2: "bij f2" "|supp f2| <o |UNIV::var set|"
      "id_on (- {x, z}) f2 \<and> id_on (FFVars (Lm x t)) f2" and 
    f2': "bij f2'" "|supp f2'| <o |UNIV::var set|"
      "id_on (- {x2', z}) f2' \<and> id_on (FFVars (Lm x2' t2')) f2'"
    and z2: "f2 x = z" "f2' x2' = z"  
    and f2f2': "rrename f2 t = rrename f2' t2'"   
    using z Lm_inject_strong'[OF 2(2), of z] by auto

    have if2': "bij (inv f2' o f2)" "|supp (inv f2' o f2)| <o |UNIV::var set|"
    by (auto simp add: f2 f2' Lterm_pre.supp_comp_bound)

    have t2': "t2' = rrename (inv f2' o f2) t" 
    using f2f2' by (metis (mono_tags, lifting) bij_imp_bij_inv f2 f2' 
      inv_o_simp1 supp_inv_bound Lterm.rrename_comps Lterm.rrename_ids)

    have fvb2': "FVarsB b2' \<subseteq> FFVars t2'"
    using Lm2[OF if2', unfolded t2'[symmetric], OF 2(1)] .

    define ff2' where "ff2' = f1 o (inv f2) o f2'"

    have ff2': "bij ff2'" "|supp ff2'| <o |UNIV::var set|"
       "id_on (- {x2', z}) ff2' \<and> id_on (FFVars (Lm x2' t2')) ff2'" 
    unfolding ff2'_def using f1 f2 f2'  
      subgoal by auto 
      subgoal unfolding ff2'_def using f1 f2 f2' by (simp add: Lterm_pre.supp_comp_bound)
      subgoal unfolding ff2'_def using f1 f2 f2' unfolding id_on_def by simp (metis inv_simp1 z1(1) z2(1)) .

    have zz2: "ff2' x2' = z"
    by (metis comp_def f2 ff2'_def inv_simp1 z1(1) z2(1) z2(2))
 
    have rew1: "rrename f1' (rrename (inv f1' \<circ> f1) t) = rrename f1 t" 
    using f1f1' t1' by auto

    have rew2: "rrename ff2' (rrename (inv f2' \<circ> f2) t) = rrename f1 t" 
    by (smt (verit, del_insts) bij_betw_imp_inj_on bij_imp_bij_inv bij_o f1(1) f1(2) f2'(1) f2'(2) f2(1) f2(2) f2f2' ff2'_def o_inv_o_cancel supp_inv_bound Lterm.rrename_comps Lterm_pre.supp_comp_bound)
 
    show "b1 = b2" unfolding 1(3) 2(3) 
    apply(rule LmB_inject_strong'_rev[OF b12', of z _ _ f1' ff2'])
      subgoal using z fvb1' by auto
      subgoal using z fvb2' by auto
      subgoal using f1' by auto  subgoal using f1' by auto
      subgoal using f1' by auto  subgoal using z1 by auto
      subgoal using ff2' by auto  subgoal using ff2' by auto
      subgoal using ff2' by auto  subgoal using zz2 by auto 
      subgoal apply(rule Lm1[OF f1(1,2)])  
        subgoal using Lm3[OF if1' 1(1)[unfolded t1'] f1'(1,2), unfolded rew1] .
        subgoal using Lm3[OF if2' 2(1)[unfolded t2'] ff2'(1,2), unfolded rew2] . . .
  (* *)
  next
    fix b y 
    assume R: "R (Lm x t) b" and yy: "y \<in> FVarsB b"
    then obtain x' t' b'
    where 0: "R t' b'" "Lm x t = Lm x' t'" "b = LmB x' b'" 
    using R_Lm_elim by metis

    have b': "b' \<in>  B"
    using 0(1,3) R_B by auto

    have y: "y \<noteq> x'" "y \<in> FVarsB b'" using b' yy unfolding 0 
    using FVarsB_LmB[OF b'] by auto

    have "|{x,x'} \<union> FFVars t \<union> FFVars t'| <o |UNIV::var set|"
    by (metis Un_insert_right singl_bound sup_bot_right Lterm.set_bd_UNIV var_Lterm_pre_class.Un_bound)
    then obtain z where z: 
    "z \<notin> {x,x'} \<union> FFVars t \<union> FFVars t'" 
    by (meson exists_fresh)

    obtain f where 
    f: "bij f" "|supp f| <o |UNIV::var set|"
       "id_on (- {x, x'}) f \<and> id_on (FFVars (Lm x t)) f" 
    and z: "f x = x'"   
    and t': "t' = rrename f t" 
    using  Lm_inject_strong[OF 0(2)] by auto
    
    have fvb't': "FVarsB b' \<subseteq> FFVars t'"
    using Lm2[OF f(1,2), unfolded t'[symmetric], OF 0(1)] .
    have yt': "y \<in> FFVars t'" using fvb't' y(2) by auto

    show "y \<in> FFVars (Lm x t)" using yt' y unfolding 0(2) by auto
  (* *)
  next
    fix b and f :: "var\<Rightarrow>var"

    assume "R (Lm x t) b" and f: "bij f" "|supp f| <o |UNIV::var set|"

   
    then obtain x' t' b'
    where 0: "R t' b'" "Lm x t = Lm x' t'" "b = LmB x' b'" 
    using R_Lm_elim by metis


    have b': "b' \<in>  B"
    using 0(1,3) R_B by auto

    have "|{x,x'} \<union> FFVars t \<union> FFVars t'| <o |UNIV::var set|"
    by (metis Un_insert_right singl_bound sup_bot_right Lterm.set_bd_UNIV var_Lterm_pre_class.Un_bound)
    then obtain z where z: 
    "z \<notin> {x,x'} \<union> FFVars t \<union> FFVars t'" 
    by (meson exists_fresh)

    obtain g where 
    g: "bij g" "|supp g| <o |UNIV::var set|"
       "id_on (- {x, x'}) g \<and> id_on (FFVars (Lm x t)) g" 
    and z: "g x = x'"   
    and t': "t' = rrename g t" 
    using Lm_inject_strong[OF 0(2)] by auto

    have RR: "R (Lm (f x') (rrename f t')) (LmB (f x') (renB f b'))"
    apply(rule R.Lm) unfolding t' apply(rule Lm3)
      subgoal by fact  subgoal by fact
      subgoal using 0(1) unfolding t' .
      subgoal by fact subgoal by fact .

    show "R (rrename f (Lm x t)) (renB f b)" 
    unfolding 0 using RR apply(subst rrename_simps) 
      subgoal using f by auto subgoal using f by auto
      subgoal apply(subst renB_LmB)
       using f b' by auto .  
  qed
qed

lemmas R_functional = R_main[THEN conjunct1]
lemmas R_FFVars = R_main[THEN conjunct2, THEN conjunct1]
lemmas R_subst = R_main[THEN conjunct2, THEN conjunct2]

definition H :: "lterm \<Rightarrow> 'b" where "H t \<equiv> SOME d. R t d"

lemma R_F: "R t (H t)"
by (simp add: R_total H_def someI_ex)

lemma ex_morFromTrm: "\<exists>H. morFromTrm H"
apply(rule exI[of _ H]) unfolding morFromTrm_def apply(intro conjI)
  subgoal using R_B R_F by auto
  subgoal using R.Vr R_F R_functional by blast
  subgoal using R.Ap R_F R_functional by blast
  subgoal using R.Lm R_F R_functional by blast
  subgoal by (meson R_F R_functional R_subst)
  subgoal by (simp add: R_F R_FFVars) .

definition rec where "rec \<equiv> SOME H. morFromTrm H"

lemma morFromTrm_rec: "morFromTrm rec"
by (metis ex_morFromTrm rec_def someI_ex)

lemma rec_B[simp,intro!]: "rec e \<in> B"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_Vr[simp]: "rec (Vr x) = VrB x"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_Ap[simp]: "rec (Ap e1 e2) = ApB (rec e1) (rec e2)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_Lm[simp]: "rec (Lm x e) = LmB x (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_rrename: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
 rec (rrename \<sigma> e) = renB \<sigma> (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma FVarsB_rec: "FVarsB (rec e) \<subseteq> FFVars e"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_unique: 
assumes "\<And>e. H e \<in> B" 
"\<And>x. H (Vr x) = VrB x" 
"\<And>e1 e2. H (Ap e1 e2) = ApB (H e1) (H e2)"
"\<And>x e. H (Lm x e) = LmB x (H e)"
shows "H = rec"
apply(rule ext) subgoal for e apply(induct e)
using assms by auto .


end (* context LC_Rec *)





end
