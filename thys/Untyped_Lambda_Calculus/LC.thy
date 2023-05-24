theory LC
  imports "../MRBNF_Recursor" "HOL-Library.FSet" "../../FixedCountableVars"
begin 

(****************************)
(* 1. GENERAL CUSTOMIZATION *)

lemmas supp_inv_bound[simp]
lemmas bij_swap[simp]
lemmas supp_id_bound[simp]

lemma fvars_subset_id_on: "supp f \<subseteq> A \<Longrightarrow> id_on (B - A) f"
  unfolding supp_def id_on_def by blast
lemma finite_singleton: "finite {x}" by blast


(****************************)
(* 2. DATATYPE DECLARTION  *)

(* binder_datatype 'a term =
  Var 'a
| App "'a term" "'a term"
| Abs x::'a t::"'a term" binds x in t
*)

declare [[inductive_internals]]

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Abs", NONE), [@{typ 'bvar}, @{typ 'brec}])
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
(* 3. DATATYPE-SPECIFIC CUSTOMIZATION  *)


(* Monomorphising: *)
instance var :: var_term_pre apply standard 
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)

type_synonym trm = "var term"


(* *)

(* Enabling some simplification rules: *)
lemmas tvsubst_VVr[simp] FVars_VVr[simp]
term.rrename_ids[simp] term.rrename_cong_ids[simp]
term.FFVars_rrenames[simp]

lemma singl_bound: "|{a}| <o |UNIV::var set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF term_pre.UNIV_cinfinite]])

lemma IImsupp_VVr_empty[simp]: "IImsupp VVr = {}"
  unfolding IImsupp_def SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
  done

(* VVr is here the Var constructor: *)
lemma VVr_eq_Var[simp]: "VVr = Var"
  unfolding VVr_def Var_def comp_def \<eta>_def
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
      apply (rule tvsubst_VVr)
      apply (rule SSupp_VVr_bound)
        done
      apply (rule trans)
       apply (rule tvsubst_cctor_not_isVVr)
          apply (rule SSupp_VVr_bound)
      unfolding IImsupp_VVr_empty
         apply (rule Int_empty_right)
      unfolding tvnoclash_term_def Int_Un_distrib Un_empty
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
  shows "rrename_term f (Var a) = Var (f a)"
    "rrename_term f (App e1 e2) = App (rrename_term f e1) (rrename_term f e2)"
    "rrename_term f (Abs x e) = Abs (f x) (rrename_term f e)"
  unfolding Var_def App_def Abs_def term.rrename_cctors[OF assms] map_term_pre_def comp_def
    Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case map_prod_def prod.case id_def
    apply (rule refl)+
  done

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

lemma Abs_inject: "(Abs x e = Abs x' e') = (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FFVars_term (Abs x e)) f \<and> f x = x' \<and> rrename_term f e = e')"
  unfolding term.set
  unfolding Abs_def term.TT_injects0 map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_term_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_term_pre_def
    Un_empty_right UN_single
  apply (rule refl)
  done

lemma bij_map_term_pre: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> bij (map_term_pre (id::var \<Rightarrow>var) f (rrename_term f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_term_pre id (inv f) (rrename_term (inv f)) id"])
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

lemma map_term_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> inv (map_term_pre (id::_::var_term_pre \<Rightarrow> _) f (rrename_term f) id) = map_term_pre id (inv f) (rrename_term (inv f)) id"
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

lemma Abs_set3: "term_ctor v = Abs (x::var) e \<Longrightarrow> \<exists>x' e'. term_ctor v = Abs x' e' \<and> x' \<in> set2_term_pre v \<and> e' \<in> set3_term_pre v"
  unfolding Abs_def term.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_term_pre id f (rrename_term f) id"])
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

lemma Abs_avoid: "|A::var set| <o |UNIV::var set| \<Longrightarrow> \<exists>x' e'. Abs x e = Abs x' e' \<and> x' \<notin> A"
  apply (drule term.TT_fresh_nchotomys[of _ "Abs x e"])
  apply (erule exE)
  apply (erule conjE)
   apply (drule sym)
  apply (frule Abs_set3)
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

lemma Abs_rrename: 
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>   
 (\<And>a'. a' \<in>FFVars_term e - {a::var} \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> Abs a e = Abs (\<sigma> a) (rrename_term \<sigma> e)"
by (metis rrename_simps(3) term.rrename_cong_ids term.set(3))


(* Bound properties (needed as auxiliaries): *)

lemma SSupp_upd_bound:
  fixes f::"var \<Rightarrow> trm"
  shows "|SSupp (f (a:=t))| <o |UNIV::var set| \<longleftrightarrow> |SSupp f| <o |UNIV::var set|"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply singl_bound ordLeq_refl split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF term_pre.Un_bound], rotated]
      intro: card_of_mono1)
  done

corollary SSupp_upd_VVr_bound[simp,intro!]: "|SSupp (VVr(a:=(t::trm)))| <o |UNIV::var set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule SSupp_VVr_bound)
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
unfolding IImsupp_def SSupp_def apply (auto simp: FFVars_tvsubst) 
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
shows "IImsupp (rrename_term (\<sigma>::var\<Rightarrow>var) o \<tau>) \<subseteq> imsupp \<sigma> \<union> IImsupp \<tau>"
unfolding IImsupp_def imsupp_def supp_def SSupp_def by force

lemma IImsupp_rrename_su': 
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|" 
shows "IImsupp (\<lambda>a. rrename_term (\<sigma>::var\<Rightarrow>var) (\<tau> a)) \<subseteq> imsupp \<sigma> \<union> IImsupp \<tau>"
using IImsupp_rrename_su[OF assms] unfolding o_def .

lemma IImsupp_rrename_bound: 
assumes s: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|" 
shows "|IImsupp (rrename_term (\<sigma>::var\<Rightarrow>var) o \<tau>)| <o |UNIV:: var set|"
using IImsupp_rrename_su[OF s(1,2)] s
by (metis SSupp_IImsupp_bound finite_Un finite_iff_le_card_var finite_subset imsupp_supp_bound infinite_var)

lemma SSupp_rrename_bound: 
assumes s: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"  
shows "|SSupp (rrename_term (\<sigma>::var\<Rightarrow>var) o \<tau>)| <o |UNIV:: var set|"
using IImsupp_rrename_bound[OF assms] 
by (metis IImsupp_def card_of_subset_bound sup_ge1)

lemma SSupp_rrename_bound': 
assumes s: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o  |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"  
shows "|SSupp (\<lambda>a. rrename_term (\<sigma>::var\<Rightarrow>var) (\<tau> a))| <o |UNIV:: var set|"
using SSupp_rrename_bound[OF assms] unfolding o_def .

(* *)
lemma SSupp_update_rrename_bound: 
"|SSupp (Var(\<sigma> (x::var) := rrename_term \<sigma> e))| <o |UNIV::var set|"
using SSupp_upd_Var_bound .

lemma IImsupp_rrename_update_su: 
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "IImsupp (rrename_term \<sigma> \<circ> Var(x := e)) \<subseteq> 
       imsupp \<sigma> \<union> {x} \<union> FFVars_term e"
unfolding IImsupp_def SSupp_def imsupp_def supp_def by (auto split: if_splits)  

lemma IImsupp_rrename_update_bound: 
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "|IImsupp (rrename_term \<sigma> \<circ> Var(x := e))| <o |UNIV::var set|"
using IImsupp_rrename_update_su[OF assms]  
by (meson Un_bound card_of_subset_bound imsupp_supp_bound infinite_var s(2) singl_bound term.set_bd_UNIV)

lemma SSupp_rrename_update_bound: 
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "|SSupp (rrename_term \<sigma> \<circ> Var(x := e))| <o |UNIV::var set|"
using IImsupp_rrename_update_bound[OF assms] 
  by (metis (mono_tags) IImsupp_def finite_Un finite_iff_le_card_var)

(* Action of swapping (a particular renaming) on variables *)

lemma rrename_swap_Var1[simp]: "rrename_term (id(x := xx, xx := x)) (Var (x::var)) = Var xx" 
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Var2[simp]: "rrename_term (id(x := xx, xx := x)) (Var (xx::var)) = Var x" 
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Var3[simp]: "z \<notin> {x,xx} \<Longrightarrow> rrename_term (id(x := xx, xx := x)) (Var (z::var)) = Var z" 
apply(subst rrename_simps(1)) by auto
lemma rrename_swap_Var[simp]: "rrename_term (id(x := xx, xx := x)) (Var (z::var)) = 
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
shows "rrename_term \<sigma> (tvsubst \<tau> e) = tvsubst (rrename_term \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_rrename_bound'[OF b s, simp]
  show ?thesis
  apply(induct e rule: term.fresh_induct[where A = "IImsupp \<tau> \<union> imsupp \<sigma>"])
    subgoal using s(1) s(2) Un_bound SSupp_IImsupp_bound imsupp_supp_bound infinite_var by blast
    subgoal by simp 
    subgoal by simp
    subgoal for x t apply simp apply(subgoal_tac "x \<notin> IImsupp (\<lambda>a. rrename_term  \<sigma> (\<tau> a))") 
      subgoal unfolding imsupp_def supp_def by simp
      subgoal using IImsupp_rrename_su' b s(1) by blast . .
qed

(* Equivariance of unary substitution: *)

lemma tvsubst_rrename_comp[simp]: 
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "tvsubst (rrename_term \<sigma> \<circ> Var(x := e2)) e1 = tvsubst (Var(\<sigma> x := rrename_term \<sigma> e2)) (rrename_term \<sigma> e1)"
proof-
  note SSupp_rrename_update_bound[OF assms, unfolded comp_def, simplified, simp]
  note SSupp_update_rrename_bound[unfolded fun_upd_def, simplified, simp] 
  show ?thesis
  apply(induct e1 rule: term.fresh_induct[where A = "{x} \<union> FFVars_term e2 \<union> imsupp \<sigma>"])
    subgoal by (meson Un_bound imsupp_supp_bound infinite_var s(2) singl_bound term.set_bd_UNIV) 
    subgoal by auto 
    subgoal by simp
    subgoal for y t apply simp apply(subgoal_tac 
      "y \<notin> IImsupp ((\<lambda>a. rrename_term \<sigma> (if a = x then e2 else Var a))) \<and> 
      \<sigma> y \<notin> IImsupp (\<lambda>a. if a = \<sigma> x then rrename_term \<sigma> e2 else Var a)") 
      subgoal unfolding imsupp_def supp_def by simp
      subgoal unfolding IImsupp_def imsupp_def SSupp_def supp_def by auto . .
qed

(* Unary substitution versus swapping: *)
lemma tvsubst_Var_rrename_term: 
assumes xx: "xx \<notin> FFVars_term e1 - {x}"
shows "tvsubst (Var((x::var) := e2)) e1 = tvsubst (Var(xx := e2)) (rrename_term (id(x := xx, xx := x)) e1)"
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
 

end