theory LC
imports "../MRBNF_Recursor" "HOL-Library.FSet"
 "../Instantiation_Infrastructure/FixedCountableVars"
 "../Instantiation_Infrastructure/Swapping_vs_Permutation"
 "../General_Customization"
 "../Prelim/More_List"
begin

context begin
ML_file \<open>../../Tools/binder_induction.ML\<close>
end


(* DATATYPE DECLARTION  *)

(* binder_datatype 'a term =
  Var 'a
| App "'a term" "'a term"
| Lam x::'a t::"'a term" binds x in t
*)

declare [[inductive_internals]]

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NONE), [@{typ 'bvar}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_mrbnfs



(****************************)
(* DATATYPE-SPECIFIC CUSTOMIZATION  *)


(* Monomorphising: *)
instance var :: var_term_pre apply standard
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)

instance var::cinf
apply standard 
  subgoal apply(rule exI[of _ "inv Variable"])
  by (simp add: bij_Variable bij_is_inj)
  subgoal using infinite_var . .

type_synonym trm = "var term"

(* Some lighter notations: *)
abbreviation "VVr \<equiv> tvVVr_tvsubst"
lemmas VVr_def = tvVVr_tvsubst_def
abbreviation "isVVr \<equiv> tvisVVr_tvsubst"
lemmas isVVr_def = tvisVVr_tvsubst_def
abbreviation "IImsupp \<equiv> tvIImsupp_tvsubst"
lemmas IImsupp_def = tvIImsupp_tvsubst_def
abbreviation "SSupp \<equiv> tvSSupp_tvsubst"
lemmas SSupp_def = tvSSupp_tvsubst_def
abbreviation "FFVars \<equiv> FFVars_term"

abbreviation "rrename \<equiv> rrename_term"
(* *)

lemma FFVars_tvsubst[simp]:
"FFVars (tvsubst \<sigma> t) = (\<Union> {FFVars (\<sigma> x) | x . x \<in> FFVars t})"
sorry (* AtoDJ: This lemma was no longer available... *)

lemma fsupp_le[simp]: 
"fsupp (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set|" 
by (simp add: finite_card_var fsupp_def supp_def)

(* *)

lemma trm_strong_induct[consumes 1, case_names Var App Lam]: 
"|A| <o |UNIV::var set|  
\<Longrightarrow>
(\<And>x. P (Var (x::var))) 
\<Longrightarrow>
(\<And>t1 t2. P t1 \<Longrightarrow> P t2 \<Longrightarrow> P (App t1 t2)) 
\<Longrightarrow> 
(\<And>x t. x \<notin> A \<Longrightarrow> P t \<Longrightarrow> P (Lam x t)) 
\<Longrightarrow> 
P t"
apply(rule term.strong_induct[of "\<lambda>\<rho>. A" "\<lambda>t \<rho>. P t", rule_format])
by auto

(* Enabling some simplification rules: *)
lemmas term.tvsubst_VVr[simp] term.FVars_VVr[simp]
term.rrename_ids[simp] term.rrename_cong_ids[simp]
term.FFVars_rrenames[simp]

lemma singl_bound: "|{a}| <o |UNIV::var set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF term_pre.UNIV_cinfinite]])

lemma ls_UNIV_iff_finite: "|A| <o |UNIV::var set| \<longleftrightarrow> finite A"
using finite_iff_le_card_var by blast

lemma supp_id_update_le[simp,intro]:
"|supp (id(x := y))| <o |UNIV::var set|"
by (metis finite.emptyI finite.insertI finite_card_var imsupp_id_fun_upd imsupp_supp_bound infinite_var)

lemma IImsupp_VVr_empty[simp]: "IImsupp VVr = {}"
  unfolding IImsupp_def
  term.SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
  done

(* VVr is here the Var constructor: *)
lemma VVr_eq_Var[simp]: "VVr = Var"
  unfolding VVr_def Var_def comp_def
  tv\<eta>_term_tvsubst_def
  by (rule refl)

(* *)
(* Properties of term-for-variable substitution *)

lemma tvsubst_VVr_func[simp]: "tvsubst VVr t = t"
  apply (rule term.TT_plain_co_induct)
  subgoal for x
    apply (rule case_split[of "isVVr (term_ctor x)"])
     apply (unfold isVVr_def)[1]
     apply (erule exE)
    subgoal premises prems for a
      unfolding prems
      apply (rule term.tvsubst_VVr)
      apply (rule term.SSupp_VVr_bound)
        done
      apply (rule trans)
       apply (rule term.tvsubst_cctor_not_isVVr)
          apply (rule term.SSupp_VVr_bound)
      unfolding IImsupp_VVr_empty
         apply (rule Int_empty_right)
      unfolding noclash_term_def Int_Un_distrib Un_empty
        apply (rule conjI)
         apply (rule iffD2[OF disjoint_iff], rule allI, rule impI, assumption)
        apply (rule iffD2[OF disjoint_iff], rule allI, rule impI)
      unfolding UN_iff Set.bex_simps
        apply (rule ballI)
        apply assumption+
      apply (rule arg_cong[of _ _ term_ctor])
      apply (rule trans)
      apply (rule term_pre.map_cong)
                 apply (rule supp_id_bound bij_id)+
           apply (assumption | rule refl)+
      unfolding id_def[symmetric] term_pre.map_id
      apply (rule refl)
      done
    done

proposition rrename_simps[simp]:
  assumes "bij (f::var \<Rightarrow> var)" "|supp f| <o |UNIV::var set|"
  shows "rrename f (Var a) = Var (f a)"
    "rrename f (App e1 e2) = App (rrename f e1) (rrename f e2)"
    "rrename f (Lam x e) = Lam (f x) (rrename f e)"
  unfolding Var_def App_def Lam_def term.rrename_cctors[OF assms] map_term_pre_def comp_def
    Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case map_prod_def prod.case id_def
    apply (rule refl)+
  done

lemma rrename_cong:
assumes "bij f" "|supp f| <o |UNIV::var set|" "bij g" "|supp g| <o |UNIV::var set|"
"(\<And>z. (z::var) \<in> FFVars P \<Longrightarrow> f z = g z)"
shows "rrename f P = rrename g P"
(* A to J: why term.rrename_cong_ids
and not the above more general thoerem? *)
using assms(5) apply(binder_induction P avoiding: "supp f" "supp g" rule: term.strong_induct)
using assms apply auto by (metis not_in_supp_alt)+

lemma tvsubst_cong:
assumes f: "|SSupp f| <o |UNIV::var set|" and g: "|SSupp g| <o |UNIV::var set|"
and eq: "(\<And>z. (z::var) \<in> FFVars P \<Longrightarrow> f z = g z)"
shows "tvsubst f P = tvsubst g P"
proof-
  have fg: "|IImsupp f| <o |UNIV::var set|" "|IImsupp g| <o |UNIV::var set|" 
    using f g  
    by (simp_all add: IImsupp_def term.card_of_FFVars_bounds 
       term_prevar_term_prevar_term_prevar_prodIDterm_prevar_prodIDsum_class.UN_bound 
       term_prevar_term_prevar_term_prevar_prodIDterm_prevar_prodIDsum_class.Un_bound) 
  have 0: "|IImsupp f \<union> IImsupp g| <o |UNIV::var set|" 
    using fg var_term_pre_class.Un_bound by blast
  show ?thesis using 0 eq apply(binder_induction P avoiding: "IImsupp f" "IImsupp g" rule: term.strong_induct)
    subgoal using fg by auto
    subgoal using fg by simp  
    subgoal using f g by simp
    subgoal using f g by simp
    subgoal using f g fg apply simp unfolding IImsupp_def SSupp_def 
    by auto metis .
qed

proposition App_inject[simp]: "(App a b = App c d) = (a = c \<and> b = d)"
proof
  assume "App a b = App c d"
  then show "a = c \<and> b = d"
    unfolding App_def fun_eq_iff term.TT_injects0
      map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
      Abs_term_pre_inject[OF UNIV_I UNIV_I]
    by blast
qed simp

proposition Var_inject[simp]: "(Var a = Var b) = (a = b)"
  apply (rule iffI[rotated])
   apply (rule arg_cong[of _ _ Var])
  apply assumption
  unfolding Var_def term.TT_injects0 map_term_pre_def comp_def map_sum_def sum.case Abs_term_pre_inverse[OF UNIV_I]
  id_def Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject
  apply (erule exE conjE)+
  apply assumption
  done

lemma Lam_inject: "(Lam x e = Lam x' e') = (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FFVars_term (Lam x e)) f \<and> f x = x' \<and> rrename f e = e')"
  unfolding term.set
  unfolding Lam_def term.TT_injects0 map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_term_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_term_pre_def
    Un_empty_right UN_single
  apply (rule refl)
  done

lemma Lam_same_inject[simp]: "Lam (x::var) e = Lam x e' \<longleftrightarrow> e = e'"
unfolding Lam_inject apply safe
apply(rule term.rrename_cong_ids[symmetric]) 
unfolding id_on_def by auto

lemma bij_map_term_pre: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> bij (map_term_pre (id::var \<Rightarrow>var) f (rrename f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_term_pre id (inv f) (rrename (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule term_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 term.rrename_comp0s term.rrename_id0s
  apply (rule term_pre.map_id0)
  apply (rule trans)
   apply (rule term_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 term.rrename_comp0s term.rrename_id0s
  apply (rule term_pre.map_id0)
  done

lemma map_term_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> inv (map_term_pre (id::_::var_term_pre \<Rightarrow> _) f (rrename f) id) = map_term_pre id (inv f) (rrename (inv f)) id"
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
  apply assumption
  apply (rule inv_unique_comp)
   apply (rule trans)
    apply (rule term_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
   defer
  apply (rule trans)
    apply (rule term_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 inv_o_simp2 term.rrename_comp0s term.rrename_id0s term_pre.map_id0
   apply (rule refl)+
  done

lemma Lam_set3: "term_ctor v = Lam (x::var) e \<Longrightarrow> \<exists>x' e'. term_ctor v = Lam x' e' \<and> x' \<in> set2_term_pre v \<and> e' \<in> set3_term_pre v"
  unfolding Lam_def term.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_term_pre id f (rrename f) id"])
     apply (rule bij_map_term_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding term.rrename_id0s term_pre.map_id map_term_pre_inv_simp
    unfolding map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_term_pre_def set3_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding term.FFVars_rrenames[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF term.rrename_bijs[OF bij_imp_bij_inv supp_inv_bound]]
  term.rrename_inv_simps[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding term.rrename_comps[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 term.rrename_ids
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+
  done
  done

lemma Lam_avoid: "|A::var set| <o |UNIV::var set| \<Longrightarrow> \<exists>x' e'. Lam x e = Lam x' e' \<and> x' \<notin> A"
  apply (drule term.TT_fresh_nchotomys[of _ "Lam x e"])
  apply (erule exE)
  apply (erule conjE)
   apply (drule sym)
  apply (frule Lam_set3)
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

lemma Lam_rrename:
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>
 (\<And>a'. a' \<in>FFVars_term e - {a::var} \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> Lam a e = Lam (\<sigma> a) (rrename \<sigma> e)"
by (metis rrename_simps(3) term.rrename_cong_ids term.set(3))


(* Bound properties (needed as auxiliaries): *)

lemma SSupp_upd_bound:
  fixes f::"var \<Rightarrow> trm"
  shows "|SSupp (f (a:=t))| <o |UNIV::var set| \<longleftrightarrow> |SSupp f| <o |UNIV::var set|"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply singl_bound ordLeq_refl fset_simps split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF term_pre.Un_bound], rotated]
      intro: card_of_mono1)  sorry


corollary SSupp_upd_VVr_bound[simp,intro!]: "|SSupp (VVr(a:=(t::trm)))| <o |UNIV::var set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule term.SSupp_VVr_bound)
  done

lemma SSupp_upd_Var_bound[simp,intro!]: "|SSupp (Var(a:=(t::trm)))| <o |UNIV::var set|"
using SSupp_upd_VVr_bound by auto

lemma supp_swap_bound[simp,intro!]: "|supp (id(x::var := xx, xx := x))| <o |UNIV:: var set|"
by (simp add: cinfinite_imp_infinite supp_swap_bound term.UNIV_cinfinite)

lemma SSupp_IImsupp_bound: "|SSupp \<sigma>| <o |UNIV:: var set| \<Longrightarrow> |IImsupp \<sigma>| <o |UNIV:: var set|"
unfolding IImsupp_def
by (simp add: var_ID_class.Un_bound term.set_bd_UNIV var_term_pre_class.UN_bound)

(* *)

lemma IImsupp_tvsubst_su:
assumes s[simp]: "|SSupp \<sigma>| <o  |UNIV:: var set|"
shows "IImsupp (tvsubst (\<sigma>::var\<Rightarrow>trm) o \<tau>) \<subseteq> IImsupp \<sigma> \<union> IImsupp \<tau>"
unfolding IImsupp_def SSupp_def apply auto
by (metis s singletonD term.set(1) term.subst(1))

lemma IImsupp_tvsubst_su':
assumes s[simp]: "|SSupp \<sigma>| <o  |UNIV:: var set|"
shows "IImsupp (\<lambda>a. tvsubst (\<sigma>::var\<Rightarrow>trm) (\<tau> a)) \<subseteq> IImsupp \<sigma> \<union> IImsupp \<tau>"
using IImsupp_tvsubst_su[OF assms] unfolding o_def .

lemma IImsupp_tvsubst_bound:
assumes s: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|IImsupp (tvsubst (\<sigma>::var\<Rightarrow>trm) o \<tau>)| <o |UNIV:: var set|"
using IImsupp_tvsubst_su[OF s(1)] s
by (meson Un_bound SSupp_IImsupp_bound card_of_subset_bound)

lemma SSupp_tvsubst_bound:
assumes s: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|SSupp (tvsubst (\<sigma>::var\<Rightarrow>trm) o \<tau>)| <o |UNIV:: var set|"
using IImsupp_tvsubst_bound[OF assms]
by (metis IImsupp_def card_of_subset_bound sup_ge1)

lemma SSupp_tvsubst_bound':
assumes s: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "|SSupp (\<lambda>a. tvsubst (\<sigma>::var\<Rightarrow>trm) (\<tau> a))| <o |UNIV:: var set|"
using SSupp_tvsubst_bound[OF assms] unfolding o_def .

(* *)

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
"|SSupp (Var(\<sigma> (x::var) := rrename \<sigma> e))| <o |UNIV::var set|"
using SSupp_upd_Var_bound .

lemma IImsupp_rrename_update_su:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "IImsupp (rrename \<sigma> \<circ> Var(x := e)) \<subseteq>
       imsupp \<sigma> \<union> {x} \<union> FFVars_term e"
unfolding IImsupp_def SSupp_def imsupp_def supp_def by (auto split: if_splits)

lemma IImsupp_rrename_update_bound:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "|IImsupp (rrename \<sigma> \<circ> Var(x := e))| <o |UNIV::var set|"
using IImsupp_rrename_update_su[OF assms]
by (meson Un_bound card_of_subset_bound imsupp_supp_bound infinite_var s(2) singl_bound term.set_bd_UNIV)

lemma SSupp_rrename_update_bound:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "|SSupp (rrename \<sigma> \<circ> Var(x := e))| <o |UNIV::var set|"
using IImsupp_rrename_update_bound[OF assms]
  by (metis (mono_tags) IImsupp_def finite_Un finite_iff_le_card_var)

(* Action of swapping (a particular renaming) on variables *)

lemma rrename_swap_Var1[simp]: "rrename (id(x := xx, xx := x)) (Var (x::var)) = Var xx"
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Var2[simp]: "rrename (id(x := xx, xx := x)) (Var (xx::var)) = Var x"
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Var3[simp]: "z \<notin> {x,xx} \<Longrightarrow> rrename (id(x := xx, xx := x)) (Var (z::var)) = Var z"
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Var[simp]: "rrename (id(x := xx, xx := x)) (Var (z::var)) =
 Var (if z = x then xx else if z = xx then x else z)"
apply(subst rrename_simps(1)) by auto

(* Compositionality properties of renaming and term-for-variable substitution *)

lemma tvsubst_comp:
assumes s[simp]: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "tvsubst (\<sigma>::var\<Rightarrow>trm) (tvsubst \<tau> e) = tvsubst (tvsubst \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_tvsubst_bound'[OF s, simp]
  show ?thesis
  apply(induct e rule: term.fresh_induct[where A = "IImsupp \<sigma> \<union> IImsupp \<tau>"])
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
  apply(induct e rule: term.fresh_induct[where A = "IImsupp \<tau> \<union> imsupp \<sigma>"])
    subgoal using s(1) s(2) Un_bound SSupp_IImsupp_bound imsupp_supp_bound infinite_var by blast
    subgoal by simp
    subgoal by simp
    subgoal for x t apply simp apply(subgoal_tac "x \<notin> IImsupp (\<lambda>a. rrename  \<sigma> (\<tau> a))")
      subgoal unfolding imsupp_def supp_def by simp
      subgoal using IImsupp_rrename_su' b s(1) by blast . .
qed


(* Unary (term-for-var) substitution versus renaming: *)

lemma supp_SSupp_Var_le[simp]: "SSupp (Var \<circ> \<sigma>) = supp \<sigma>" 
unfolding supp_def SSupp_def by simp

lemma rrename_eq_tvsubst_Var: 
assumes "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|" 
shows "rrename \<sigma> = tvsubst (Var o \<sigma>)"
proof
  fix t 
  have 0: "|supp \<sigma>| <o |UNIV::var set|" using assms by auto
  have 00: " |IImsupp (Var \<circ> \<sigma>)| <o |UNIV::var set|" 
    using SSupp_IImsupp_bound by (metis "0" supp_SSupp_Var_le)
  show "rrename \<sigma> t = tvsubst (Var o \<sigma>) t" using 00 assms apply(induct t rule: trm_strong_induct)
    subgoal for x by (simp add: "0")
    subgoal by auto
    subgoal for x t 
    by (simp add: IImsupp_def disjoint_iff not_in_supp_alt) . 
qed
     
lemma rrename_eq_tvsubst_Var': 
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> rrename \<sigma> e = tvsubst (Var o \<sigma>) e"
using rrename_eq_tvsubst_Var by auto

(* Equivariance of unary substitution: *)

lemma tvsubst_rrename_comp[simp]:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "tvsubst (rrename \<sigma> \<circ> Var(x := e2)) e1 = tvsubst (Var(\<sigma> x := rrename \<sigma> e2)) (rrename \<sigma> e1)"
proof-
  note SSupp_rrename_update_bound[OF assms, unfolded comp_def, simplified, simp]
  note SSupp_update_rrename_bound[unfolded fun_upd_def, simplified, simp]
  show ?thesis
  apply(induct e1 rule: term.fresh_induct[where A = "{x} \<union> FFVars_term e2 \<union> imsupp \<sigma>"])
    subgoal by (meson Un_bound imsupp_supp_bound infinite_var s(2) singl_bound term.set_bd_UNIV)
    subgoal by auto
    subgoal by simp
    subgoal for y t apply simp apply(subgoal_tac
      "y \<notin> IImsupp ((\<lambda>a. rrename \<sigma> (if a = x then e2 else Var a))) \<and>
      \<sigma> y \<notin> IImsupp (\<lambda>a. if a = \<sigma> x then rrename \<sigma> e2 else Var a)")
      subgoal unfolding imsupp_def supp_def by simp
      subgoal unfolding IImsupp_def imsupp_def SSupp_def supp_def by auto . .
qed

(* Unary substitution versus swapping: *)
lemma tvsubst_Var_rrename:
assumes xx: "xx \<notin> FFVars_term e1 - {x}"
shows "tvsubst (Var((x::var) := e2)) e1 = tvsubst (Var(xx := e2)) (rrename (id(x := xx, xx := x)) e1)"
proof-
  show ?thesis using xx
  apply(induct e1 rule: term.fresh_induct[where A = "{x,xx} \<union> FFVars_term e2"])
    subgoal by (metis insert_is_Un term.set(1) term.set(2) term.set_bd_UNIV)
    subgoal by simp
    subgoal by auto
    subgoal for y t apply simp apply(subgoal_tac
      "y \<notin> IImsupp (Var(x := e2)) \<and> y \<notin> IImsupp (Var(xx := e2))")
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
  note term_vvsubst_rrename[simp del]
  show ?thesis using assms
  apply(subst term_vvsubst_rrename[symmetric]) apply auto
  apply(subst term.map_comp) apply auto
  apply(subst term_vvsubst_rrename[symmetric]) apply auto
  apply(subst term.map_comp) apply auto
  apply(rule term.map_cong0)
    using term_pre.supp_comp_bound by auto
qed

lemma rrename_o_swap:
"rrename (id(y::var := yy, yy := y) o id(x := xx, xx := x)) t =
 swap (swap t x xx) y yy"
apply(subst term.rrename_comps[symmetric])
by auto

(* *)

lemma swap_simps[simp]: "swap (Var z) (y::var) x = Var (sw z y x)"
"swap (App t s) (y::var) x = App(swap t y x) (swap s y x)"
"swap (Lam v t) (y::var) x = Lam (sw v y x) (swap t y x)"
by (auto simp: sw_def)

lemma FFVars_swap[simp]: "FFVars (swap t y x) =
 (\<lambda>u. sw u x y) ` (FFVars t)"
apply(subst term.FFVars_rrenames) by (auto simp: sw_def)

lemma FFVars_swap'[simp]: "{x::var,y} \<inter> FFVars t = {} \<Longrightarrow> swap t x y = t"
apply(rule term.rrename_cong_ids) by auto

(* *)

lemma Lam_inject_swap: "Lam v t = Lam v' t' \<longleftrightarrow>
  (v' \<notin> FFVars t \<or> v' = v) \<and> swap t v' v = t'"
unfolding Lam_inject apply(rule iffI)
  subgoal unfolding id_on_def apply auto
  apply(rule rrename_cong) by auto
  subgoal apply clarsimp
  apply(rule exI[of _ "id(v':=v,v:=v')"]) unfolding id_on_def by auto .

lemma Lam_inject_swap': "Lam v t = Lam v' t' \<longleftrightarrow>
  (\<exists>z. (z \<notin> FFVars t \<or> z = v) \<and> (z \<notin> FFVars t' \<or> z = v') \<and>
       swap t z v = swap t' z v')"
unfolding Lam_inject_swap apply(rule iffI)
  subgoal apply clarsimp apply(rule exI[of _ v']) by auto
  subgoal by (smt (verit, del_insts) Lam_inject_swap)    .

lemma Lam_refresh': "v' \<notin> FFVars t \<or> v' = v \<Longrightarrow>
   Lam v t = Lam v' (swap t v' v)"
using Lam_inject_swap by auto

lemma Lam_refresh:
"xx \<notin> FFVars t \<or> xx = x \<Longrightarrow> Lam x t = Lam xx (swap t x xx)"
by (metis Lam_inject_swap fun_upd_twist)

(* *)

lemma FFVars_usub[simp]: "FFVars (usub t y x) =
 (if x \<in> FFVars t then FFVars t - {x} \<union> {y} else FFVars t)"
apply(subst term.set_map) by auto

lemma usub_simps_free[simp]: "\<And>y x. usub (Var z) (y::var) x = Var (sb z y x)"
"\<And>y x t s. usub (App t s) (y::var) x = App (usub t y x) (usub s y x)"
by (auto simp: sb_def)

lemma usub_Lam[simp]:
"v \<notin> {x,y} \<Longrightarrow> usub (Lam v t) (y::var) x = Lam v (usub t y x)"
apply(subst term.map)
  subgoal by auto
  subgoal by (auto simp: imsupp_def supp_def)
  subgoal by auto .

lemmas usub_simps = usub_simps_free usub_Lam

(* *)

lemma rrename_usub[simp]:
assumes \<sigma>: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
shows "rrename \<sigma> (usub t u (x::var)) = usub (rrename \<sigma> t) (\<sigma> u) (\<sigma> x)"
using assms
apply(binder_induction t avoiding: "supp \<sigma>" u x rule: term.strong_induct)
using assms by (auto simp: sb_def)

lemma sw_sb:
"sw (sb z u x) z1 z2 = sb (sw z z1 z2) (sw u z1 z2) (sw x z1 z2)"
unfolding sb_def sw_def by auto


lemma swap_usub:
"swap (usub t (u::var) x) z1 z2 = usub (swap t z1 z2) (sw u z1 z2) (sw x z1 z2)"
apply(binder_induction t avoiding: u x z1 z2 rule: term.strong_induct)
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
  note term_vvsubst_rrename[simp del]
  show ?thesis using assms
  apply(subst term_vvsubst_rrename[symmetric]) apply simp
    subgoal by auto
    subgoal apply(subst term.map_comp)
      subgoal by auto
      subgoal by auto
      subgoal apply(rule term.map_cong0)
      using term_pre.supp_comp_bound by auto . .
qed

lemma swap_commute:
"{y,yy} \<inter> {x,xx} = {} \<Longrightarrow>
 swap (swap t y yy) x xx = swap (swap t x xx) y yy"
apply(subst term.rrename_comps)
apply auto
apply(subst term.rrename_comps)
apply auto
apply(rule rrename_cong)
by (auto simp: term_pre.supp_comp_bound)


(* *)

term "swappingFvars swap FFVars"
term "permutFvars (\<lambda>f t. rrename t f) FFVars"

lemma swappingFvars_swap_FFVars: "swappingFvars swap FFVars"
unfolding swappingFvars_def apply auto
  apply (metis id_swapTwice rrename_o_swap term.rrename_ids) 
  using sw_invol2 apply metis 
  by (metis (no_types, lifting) image_iff sw_invol2)

lemma nswapping_swap: "nswapping swap"
unfolding nswapping_def apply auto
apply (metis id_swapTwice rrename_o_swap term.rrename_ids)
by (metis id_swapTwice2 rrename_o_swap)

lemma permutFvars_rrename_FFVar: "permutFvars (\<lambda>t f. rrename f (t::trm)) FFVars"
unfolding permutFvars_def apply auto
  apply (simp add: finite_iff_le_card_var fsupp_def supp_def term.rrename_comps) 
  apply (simp add: finite_iff_le_card_var fsupp_def supp_def)
  apply (simp add: finite_iff_le_card_var fsupp_def image_in_bij_eq supp_def) .

lemma permut_rrename: "permut (\<lambda>t f. rrename f (t::trm))"
unfolding permut_def apply auto
by (simp add: finite_iff_le_card_var fsupp_def supp_def term.rrename_comps)

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
definition "mkSubst xs es \<equiv> \<lambda>x. if distinct xs \<and> x \<in> set xs then nth es (theN xs x) else Var x"

lemma mkSubst_nth[simp]: "distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> mkSubst xs es (nth xs i) = nth es i"
unfolding mkSubst_def by auto

lemma mkSubst_idle[simp]: "\<not> distinct xs \<or> \<not> x \<in> set xs \<Longrightarrow> mkSubst xs es x = Var x"
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
|SSupp (tvsubst (rrename \<sigma> \<circ> mkSubst xs es \<circ> inv \<sigma>) \<circ> (Var \<circ> \<sigma>))| <o |UNIV::var set|"
by (metis SSupp_tvsubst_bound SSupp_mkSubst mkSubst_map_rrename_inv supp_SSupp_Var_le)

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

thm Lam_inject[no_vars]

lemma Lam_inject_strong:
assumes "Lam (x::var) e = Lam x' e'"
shows "\<exists>f. bij f \<and> |supp f| <o |UNIV::var set| \<and>  
   id_on (- {x,x'}) f \<and> id_on (FFVars (Lam x e)) f \<and>
   f x = x' \<and> rrename f e = e'" 
apply(rule exI[of _ "id(x := x', x' := x)"])
using assms unfolding Lam_inject_swap apply safe
unfolding id_on_def by auto (metis fun_upd_twist)


lemma Lam_inject_strong':
assumes il: "Lam (x::var) e = Lam x' e'" and z: "z \<notin> FFVars (Lam x e) \<union> FFVars (Lam x' e')"
shows 
"\<exists>f f'. 
   bij f \<and> |supp f| <o |UNIV::var set| \<and> id_on (- {x,z}) f \<and> id_on (FFVars (Lam x e)) f \<and> f x = z \<and> 
   bij f' \<and> |supp f'| <o |UNIV::var set| \<and> id_on (- {x',z}) f' \<and> id_on (FFVars (Lam x' e')) f' \<and> f' x' = z \<and> 
   rrename f e = rrename f' e'"
proof-
  define f where "f = id(x := z, z := x)"
  have f: "bij f \<and> |supp f| <o |UNIV::var set| \<and> id_on (- {x,z}) f \<and> id_on (FFVars (Lam x e)) f \<and> f x = z"
  using z unfolding f_def id_on_def by auto
  define f' where "f' = id(x' := z, z := x')"
  have f': "bij f' \<and> |supp f'| <o |UNIV::var set| \<and> id_on (- {x',z}) f' \<and> id_on (FFVars (Lam x' e')) f' \<and> f' x' = z"
  using z unfolding f'_def id_on_def by auto
 
  obtain g where g: "bij g \<and> |supp g| <o |UNIV::var set| \<and> id_on (FFVars (Lam x e)) g \<and> g x = x'" and ge: "e' = rrename g e"
  using il unfolding Lam_inject by auto

  have ff': "rrename f e = rrename f' e'" 
  unfolding f_def f'_def ge unfolding f_def f'_def using g apply(subst term.rrename_comps)
    subgoal by auto  subgoal by auto subgoal by auto subgoal by auto
    subgoal apply(rule rrename_cong) using g
      subgoal by auto  subgoal by auto subgoal by auto 
      subgoal using term_pre.supp_comp_bound by auto
      subgoal using term_pre.supp_comp_bound z unfolding id_on_def by auto . .

  show ?thesis
  apply(rule exI[of _ f]) apply(rule exI[of _ f'])
  using f f' ff' by auto
qed


thm term.induct[no_vars]

lemma trm_rrename_induct[case_names Var App Lam]:
assumes "\<And>x. P (Var (x::var))"
and "\<And>e1 e2. P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (App e1 e2)" 
and "\<And>x e. (\<And>f. bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow> P (rrename f e)) \<Longrightarrow> P (Lam x e)"
shows "P t"
sorry

(* RECURSOR *)

locale LC_Rec = 
fixes B :: "'b set"
and VarB :: "var \<Rightarrow> 'b" 
and AppB :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
and LamB :: "var \<Rightarrow> 'b \<Rightarrow> 'b"
and renB :: "(var \<Rightarrow> var) \<Rightarrow> 'b \<Rightarrow> 'b"
and FVarsB :: "'b \<Rightarrow> var set"
assumes 
(* closedness: *)
VarB_B[simp,intro]: "\<And>x. VarB x \<in> B"
and 
AppB_B[simp,intro]: "\<And>b1 b2. {b1,b2} \<subseteq> B \<Longrightarrow> AppB b1 b2 \<in> B"
and 
LamB_B[simp,intro]: "\<And>x b. b \<in>  B \<Longrightarrow> LamB x b \<in> B"
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
and 
renB_FVarsB[simp]: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b"
and 
(* *)
renB_VarB[simp]: "\<And>\<sigma> x. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> renB \<sigma> (VarB x) = VarB (\<sigma> x)"
and 
renB_AppB[simp]: "\<And>\<sigma> b1 b2. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> {b1,b2} \<subseteq> B \<Longrightarrow> 
   renB \<sigma> (AppB b1 b2) = AppB (renB \<sigma> b1) (renB \<sigma> b2)"
and 
renB_LamB[simp]: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> b \<in> B \<Longrightarrow> 
   renB \<sigma> (LamB x b) = LamB (\<sigma> x) (renB \<sigma> b)"
(* *)
and 
FVarsB_VarB: "\<And>x. FVarsB (VarB x) \<subseteq> {x}"
and 
FVarsB_AppB: "\<And>b1 b2. {b1,b2} \<subseteq> B \<Longrightarrow> FVarsB (AppB b1 b2) \<subseteq> FVarsB b1 \<union> FVarsB b2"
and 
FVarsB_LamB: "\<And>x b. b \<in> B \<Longrightarrow> FVarsB (LamB x b) \<subseteq> FVarsB b - {x}"
begin 



definition morFromTrm where 
"morFromTrm H \<equiv> 
 (\<forall>e. H e \<in> B) \<and>  
 (\<forall>x. H (Var x) = VarB x) \<and> 
 (\<forall>e1 e2. H (App e1 e2) = AppB (H e1) (H e2)) \<and> 
 (\<forall>x e. H (Lam x e) = LamB x (H e)) \<and> 
 (\<forall>\<sigma> e. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<longrightarrow> H (rrename \<sigma> e) = renB \<sigma> (H e)) \<and> 
 (\<forall>e. FVarsB (H e) \<subseteq> FFVars e)"

inductive R where 
Var: "R (Var x) (VarB x)"
|
App: "R e1 b1 \<Longrightarrow> R e2 b2 \<Longrightarrow> R (App e1 e2) (AppB b1 b2)"
|
Lam: "R e b \<Longrightarrow> R (Lam x e) (LamB x b)"

term R


thm Lam_inject_strong[no_vars]

lemma not_in_FVarsB_LamB: "b \<in> B \<Longrightarrow> x \<notin> FVarsB (LamB x b)"
using FVarsB_LamB by auto

lemma LamB_inject_strong_rev: 
assumes bb': "{b,b'} \<subseteq> B" and 
x': "x' = x \<or> x' \<notin> FVarsB b" and 
f: "bij f" "|supp f| <o |UNIV::var set|" 
"id_on (- {x, x'}) f" "f x = x'" and r: "renB f b = b'"
shows "LamB x b = LamB x' b'"
proof-
  have id: "id_on (FVarsB (LamB x b)) f"
  using f FVarsB_LamB bb' x' unfolding id_on_def by auto
  have "LamB x b = renB f (LamB x b)"
  apply(rule sym) apply(rule renB_cong) using f bb' FVarsB_LamB unfolding id_on_def 
  using id unfolding id_on_def by auto
  also have "\<dots> = LamB x' b'" apply(subst renB_LamB) using f r bb' by auto
  finally show ?thesis .
qed

lemma LamB_inject_strong'_rev: 
assumes bb': "{b,b'} \<subseteq> B"  
and z: "z = x \<or> z \<notin> FVarsB b" "z = x' \<or> z \<notin> FVarsB b'"
and f: "bij f" "|supp f| <o |UNIV::var set|" "id_on (- {x, z}) f" "f x = z" 
and f': "bij f'" "|supp f'| <o |UNIV::var set|" "id_on (- {x', z}) f'" "f' x' = z" 
and r: "renB f b = renB f' b'"
shows "LamB x b = LamB x' b'" 
proof-
  define c where c: "c = renB f b"
  have c': "c = renB f' b'" unfolding c r ..
  have "LamB x b = LamB z c"  
  apply(rule LamB_inject_strong_rev[of _ _ _ _ f]) 
  using assms FVarsB_LamB id_on_def unfolding c by auto
  also have "LamB z c = LamB x' b'"  
  apply(rule sym, rule LamB_inject_strong_rev[of _ _ _ _ f']) 
  using assms FVarsB_LamB id_on_def unfolding c by auto
  finally show ?thesis .
qed
  
(* *)

lemma R_Var_elim[simp]: "R (Var x) b \<longleftrightarrow> b = VarB x"
apply safe
  subgoal using R.cases by fastforce
  subgoal by (auto intro: R.intros) .

lemma R_App_elim: 
assumes "R (App t1 t2) b"
shows "\<exists>b1 b2. R t1 b1 \<and> R t2 b2 \<and> b = AppB b1 b2"
by (metis App_inject R.simps assms term.distinct(1) term.distinct(4))

lemma R_Lam_elim: 
assumes "R (Lam x t) b"
shows "\<exists>x' t' e. R t' e \<and> Lam x t = Lam x' t' \<and> b = LamB x' e"
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
proof(induct e rule: trm_rrename_induct)
  case (Var x)
  then show ?case using FVarsB_VarB by auto
next
  case (App e1 e2)
  then show ?case apply safe 
    subgoal by (metis R_App_elim)
    subgoal by simp (smt (verit, del_insts) FVarsB_AppB R_App_elim 
      R_B Un_iff bot.extremum insert_Diff insert_subset)
    subgoal apply(drule R_App_elim) 
      by (smt (verit, del_insts) R.simps R_B bot.extremum insert_subset renB_AppB 
      rrename_simps(2)) .
next
  case (Lam x t)
  note Lamm = Lam[rule_format]
  note Lam1 = Lamm[THEN conjunct1, rule_format]
  note Lam2 = Lamm[THEN conjunct2, THEN conjunct1, rule_format]
  note Lam3 = Lamm[THEN conjunct2, THEN conjunct2, rule_format, OF _ _ conjI, OF _ _ _ conjI]
  note Lam33 = Lam3[of id, simplified]

  show ?case proof safe
    fix b1 b2 assume RLam: "R (Lam x t) b1" "R (Lam x t) b2" 
    then obtain x1' t1' b1' x2' t2' b2'
    where 1: "R t1' b1'" "Lam x t = Lam x1' t1'" "b1 = LamB x1' b1'"
    and   2: "R t2' b2'" "Lam x t = Lam x2' t2'" "b2 = LamB x2' b2'"
    using R_Lam_elim by metis

    have b12': "{b1',b2'} \<subseteq> B"
    using 1(1,3) 2(1,3) R_B by auto

    have "|{x,x1',x2'} \<union> FFVars t \<union> FFVars t1' \<union> FFVars t2'| <o |UNIV::var set|"
    by (metis Un_insert_right singl_bound sup_bot_right term.set_bd_UNIV var_term_pre_class.Un_bound)
    then obtain z where z: 
    "z \<notin> {x,x1',x2'} \<union> FFVars t \<union> FFVars t1' \<union> FFVars t2'" 
    by (meson exists_fresh)

    obtain f1 f1' where 
    f1: "bij f1" "|supp f1| <o |UNIV::var set|"
       "id_on (- {x, z}) f1 \<and> id_on (FFVars (Lam x t)) f1" and 
    f1': "bij f1'" "|supp f1'| <o |UNIV::var set|"
       "id_on (- {x1', z}) f1' \<and> id_on (FFVars (Lam x1' t1')) f1'"
    and z1: "f1 x = z" "f1' x1' = z"  
    and f1f1': "rrename f1 t = rrename f1' t1'"   
    using z Lam_inject_strong'[OF 1(2), of z] by auto

    have if1': "bij (inv f1' o f1)" "|supp (inv f1' o f1)| <o |UNIV::var set|"
    by (auto simp add: f1 f1' term_pre.supp_comp_bound)

    have t1': "t1' = rrename (inv f1' o f1) t"  
    using f1f1' by (metis (mono_tags, lifting) bij_imp_bij_inv f1 f1' 
       inv_o_simp1 supp_inv_bound term.rrename_comps term.rrename_ids)

    have fvb1': "FVarsB b1' \<subseteq> FFVars t1'"
    using Lam2[OF if1', unfolded t1'[symmetric], OF 1(1)] .

    obtain f2 f2' where 
    f2: "bij f2" "|supp f2| <o |UNIV::var set|"
      "id_on (- {x, z}) f2 \<and> id_on (FFVars (Lam x t)) f2" and 
    f2': "bij f2'" "|supp f2'| <o |UNIV::var set|"
      "id_on (- {x2', z}) f2' \<and> id_on (FFVars (Lam x2' t2')) f2'"
    and z2: "f2 x = z" "f2' x2' = z"  
    and f2f2': "rrename f2 t = rrename f2' t2'"   
    using z Lam_inject_strong'[OF 2(2), of z] by auto

    have if2': "bij (inv f2' o f2)" "|supp (inv f2' o f2)| <o |UNIV::var set|"
    by (auto simp add: f2 f2' term_pre.supp_comp_bound)

    have t2': "t2' = rrename (inv f2' o f2) t" 
    using f2f2' by (metis (mono_tags, lifting) bij_imp_bij_inv f2 f2' 
      inv_o_simp1 supp_inv_bound term.rrename_comps term.rrename_ids)

    have fvb2': "FVarsB b2' \<subseteq> FFVars t2'"
    using Lam2[OF if2', unfolded t2'[symmetric], OF 2(1)] .

    define ff2' where "ff2' = f1 o (inv f2) o f2'"

    have ff2': "bij ff2'" "|supp ff2'| <o |UNIV::var set|"
       "id_on (- {x2', z}) ff2' \<and> id_on (FFVars (Lam x2' t2')) ff2'" 
    unfolding ff2'_def using f1 f2 f2'  
      subgoal by auto 
      subgoal unfolding ff2'_def using f1 f2 f2' by (simp add: term_pre.supp_comp_bound)
      subgoal unfolding ff2'_def using f1 f2 f2' unfolding id_on_def by simp (metis inv_simp1 z1(1) z2(1)) .

    have zz2: "ff2' x2' = z"
    by (metis comp_def f2 ff2'_def inv_simp1 z1(1) z2(1) z2(2))
 
    have rew1: "rrename f1' (rrename (inv f1' \<circ> f1) t) = rrename f1 t" 
    using f1f1' t1' by auto

    have rew2: "rrename ff2' (rrename (inv f2' \<circ> f2) t) = rrename f1 t" 
    by (smt (verit, del_insts) bij_betw_imp_inj_on bij_imp_bij_inv bij_o f1(1) f1(2) f2'(1) f2'(2) f2(1) f2(2) f2f2' ff2'_def o_inv_o_cancel supp_inv_bound term.rrename_comps term_pre.supp_comp_bound)
 
    show "b1 = b2" unfolding 1(3) 2(3) 
    apply(rule LamB_inject_strong'_rev[OF b12', of z _ _ f1' ff2'])
      subgoal using z fvb1' by auto
      subgoal using z fvb2' by auto
      subgoal using f1' by auto  subgoal using f1' by auto
      subgoal using f1' by auto  subgoal using z1 by auto
      subgoal using ff2' by auto  subgoal using ff2' by auto
      subgoal using ff2' by auto  subgoal using zz2 by auto 
      subgoal apply(rule Lam1[OF f1(1,2)])  
        subgoal using Lam3[OF if1' 1(1)[unfolded t1'] f1'(1,2), unfolded rew1] .
        subgoal using Lam3[OF if2' 2(1)[unfolded t2'] ff2'(1,2), unfolded rew2] . . .
  (* *)
  next
    fix b y 
    assume R: "R (Lam x t) b" and yy: "y \<in> FVarsB b"
    then obtain x' t' b'
    where 0: "R t' b'" "Lam x t = Lam x' t'" "b = LamB x' b'" 
    using R_Lam_elim by metis

    have b': "b' \<in>  B"
    using 0(1,3) R_B by auto

    have y: "y \<noteq> x'" "y \<in> FVarsB b'" using b' yy unfolding 0 
    using FVarsB_LamB[OF b'] by auto

    have "|{x,x'} \<union> FFVars t \<union> FFVars t'| <o |UNIV::var set|"
    by (metis Un_insert_right singl_bound sup_bot_right term.set_bd_UNIV var_term_pre_class.Un_bound)
    then obtain z where z: 
    "z \<notin> {x,x'} \<union> FFVars t \<union> FFVars t'" 
    by (meson exists_fresh)

    obtain f where 
    f: "bij f" "|supp f| <o |UNIV::var set|"
       "id_on (- {x, x'}) f \<and> id_on (FFVars (Lam x t)) f" 
    and z: "f x = x'"   
    and t': "t' = rrename f t" 
    using  Lam_inject_strong[OF 0(2)] by auto
    
    have fvb't': "FVarsB b' \<subseteq> FFVars t'"
    using Lam2[OF f(1,2), unfolded t'[symmetric], OF 0(1)] .
    have yt': "y \<in> FFVars t'" using fvb't' y(2) by auto

    show "y \<in> FFVars (Lam x t)" using yt' y unfolding 0(2) by auto
  (* *)
  next
    fix b and f :: "var\<Rightarrow>var"

    assume "R (Lam x t) b" and f: "bij f" "|supp f| <o |UNIV::var set|"

   
    then obtain x' t' b'
    where 0: "R t' b'" "Lam x t = Lam x' t'" "b = LamB x' b'" 
    using R_Lam_elim by metis


    have b': "b' \<in>  B"
    using 0(1,3) R_B by auto

    have "|{x,x'} \<union> FFVars t \<union> FFVars t'| <o |UNIV::var set|"
    by (metis Un_insert_right singl_bound sup_bot_right term.set_bd_UNIV var_term_pre_class.Un_bound)
    then obtain z where z: 
    "z \<notin> {x,x'} \<union> FFVars t \<union> FFVars t'" 
    by (meson exists_fresh)

    obtain g where 
    g: "bij g" "|supp g| <o |UNIV::var set|"
       "id_on (- {x, x'}) g \<and> id_on (FFVars (Lam x t)) g" 
    and z: "g x = x'"   
    and t': "t' = rrename g t" 
    using Lam_inject_strong[OF 0(2)] by auto

    have RR: "R (Lam (f x') (rrename f t')) (LamB (f x') (renB f b'))"
    apply(rule R.Lam) unfolding t' apply(rule Lam3)
      subgoal by fact  subgoal by fact
      subgoal using 0(1) unfolding t' .
      subgoal by fact subgoal by fact .

    show "R (rrename f (Lam x t)) (renB f b)" 
    unfolding 0 using RR apply(subst rrename_simps) 
      subgoal using f by auto subgoal using f by auto
      subgoal apply(subst renB_LamB)
       using f b' by auto .  
  qed
qed

lemmas R_functional = R_main[THEN conjunct1]
lemmas R_FFVars = R_main[THEN conjunct2, THEN conjunct1]
lemmas R_subst = R_main[THEN conjunct2, THEN conjunct2]

definition H :: "trm \<Rightarrow> 'b" where "H t \<equiv> SOME d. R t d"

lemma R_F: "R t (H t)"
by (simp add: R_total H_def someI_ex)

lemma ex_morFromTrm: "\<exists>H. morFromTrm H"
apply(rule exI[of _ H]) unfolding morFromTrm_def apply(intro conjI)
  subgoal using R_B R_F by auto
  subgoal using R.Var R_F R_functional by blast
  subgoal using R.App R_F R_functional by blast
  subgoal using R.Lam R_F R_functional by blast
  subgoal by (meson R_F R_functional R_subst)
  subgoal by (simp add: R_F R_FFVars) .

definition rec where "rec \<equiv> SOME H. morFromTrm H"

lemma morFromTrm_rec: "morFromTrm rec"
by (metis ex_morFromTrm rec_def someI_ex)

lemma rec_B[simp,intro!]: "rec e \<in> B"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_Var[simp]: "rec (Var x) = VarB x"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_App[simp]: "rec (App e1 e2) = AppB (rec e1) (rec e2)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_Lam[simp]: "rec (Lam x e) = LamB x (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_rrename: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
 rec (rrename \<sigma> e) = renB \<sigma> (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma FVarsB_rec: "FVarsB (rec e) \<subseteq> FFVars e"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_unique: 
assumes "\<And>e. H e \<in> B" 
"\<And>x. H (Var x) = VarB x" 
"\<And>e1 e2. H (App e1 e2) = AppB (H e1) (H e2)"
"\<And>x e. H (Lam x e) = LamB x (H e)"
shows "H = rec"
apply(rule ext) subgoal for e apply(induct e)
using assms by auto .


end (* context LC_Rec *)





end