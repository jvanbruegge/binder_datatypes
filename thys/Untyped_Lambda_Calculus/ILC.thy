theory ILC
imports "../MRBNF_Recursor" "HOL-Library.Stream"
 "../Instantiation_Infrastructure/FixedUncountableVars"
 "../Instantiation_Infrastructure/Swapping_vs_Permutation"
 "../General_Customization"
begin


lemmas stream.set_map[simp] lemmas stream.map_id[simp]

context begin
ML_file \<open>../../Tools/binder_induction.ML\<close>
end

(* DATATYPE DECLARTION  *)

declare [[inductive_internals]]

(*infinitary untyped lambda calculus*)
(* binder_datatype 'a iterm =
  Bot
| Var 'a
| App "'a iterm" "'a iterm cinfmset"
| Abs "X::'a cinfset" "t::'a iterm" binds X in t
*)

ML \<open>
val ctors = [
  (("iVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("iApp", NONE), [@{typ 'rec}, @{typ "'rec stream"}]),
  (("iAbs", NONE), [@{typ "'bvar stream"}, @{typ 'brec}])
]

val spec_iterm = {
  fp_b = @{binding "iterm"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding ivvsubst},
  tvsubst_b = @{binding itvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open> MRBNF_Sugar.create_binder_datatype spec_iterm \<close>
print_mrbnfs

lemma ex_inj_infinite_regular_var_iterm_pre:
  "\<exists>f :: 'a :: countable \<Rightarrow> 'b :: var_iterm_pre. inj f"
  unfolding card_of_ordLeq[of UNIV UNIV, simplified]
  apply (rule ordLeq_transitive[OF _ large])
  apply (rule ordLeq_transitive[OF countable_card_le_natLeq[THEN iffD1]])
  apply simp
  apply (rule natLeq_ordLeq_cinfinite)
  apply (rule iterm_pre.bd_Cinfinite)
  done

definition embed :: "'a :: countable \<Rightarrow> 'b :: var_iterm_pre"
  ("{{_}}" [999] 1000)  where
  "embed = (SOME f. inj f)"

lemma inj_embed: "inj embed"
  unfolding embed_def
  by (rule someI_ex[OF ex_inj_infinite_regular_var_iterm_pre[where 'a='a]])

abbreviation "ifv \<equiv> FFVars_iterm"



(****************************)
(* DATATYPE-SPECIFIC CUSTOMIZATION  *)


(* Monomorphising: *)

lemma bd_iterm_pre_ordIso: "bd_iterm_pre =o card_suc natLeq"
  apply (rule ordIso_symmetric)  
  apply (tactic \<open>BNF_Tactics.unfold_thms_tac @{context} [Thm.axiom @{theory} "ILC.iterm_pre.bd_iterm_pre_def"]\<close>)
  apply (rule ordIso_transitive[OF _ dir_image_ordIso])
    apply (rule ordIso_symmetric)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Cinfinite_csum Field_natLeq natLeq_card_order natLeq_cinfinite)
      apply (simp add: infinite_regular_card_order.Cnotzero infinite_regular_card_order_natLeq)
     apply (simp add: Field_natLeq natLeq_card_order ordLeq_csum1)
    apply (rule ordIso_transitive)
     apply (rule csum_absorb2)
      apply (simp add: Card_order_cprod Cinfinite_csum1 cinfinite_cprod natLeq_Cinfinite)
     apply (simp add: Card_order_cprod Cinfinite_csum1 cinfinite_cprod natLeq_Cinfinite natLeq_ordLeq_cinfinite)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Card_order_csum cinfinite_cprod cinfinite_csum natLeq_Cinfinite)
      apply (simp add: infinite_regular_card_order.Cnotzero infinite_regular_card_order_natLeq)
     apply (simp add: Card_order_csum cinfinite_cprod cinfinite_csum natLeq_Cinfinite natLeq_ordLeq_cinfinite)
    apply (rule ordIso_transitive)
     apply (rule csum_absorb2) 
      apply (simp add: Card_order_cprod cinfinite_cprod cinfinite_csum natLeq_Cinfinite) 
      (*
     apply (simp add: cprod_cong1 csum_com ordIso_imp_ordLeq)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Card_order_csum cinfinite_csum natLeq_Cinfinite)
      apply (simp add: lam_pre.bd_Cnotzero)
     apply (simp add: natLeq_Cinfinite ordLeq_csum2)
    apply (simp add: csum_absorb1 infinite_regular_card_order.Card_order infinite_regular_card_order.cinfinite infinite_regular_card_order_card_suc natLeq_Cinfinite natLeq_card_order natLeq_ordLeq_cinfinite)
  using Card_order_cprod card_order_on_well_order_on apply blast
  apply (simp add: inj_on_def Abs_iterm_pre_bdT_inject)
  done
*) sorry

lemma natLeq_less_UNIV: "natLeq <o |UNIV :: 'a :: var_iterm_pre set|"
  apply (rule ordLess_ordLeq_trans[OF _ iterm.var_large])
  apply (rule ordLess_ordIso_trans[OF card_suc_greater[OF natLeq_card_order]])
  apply (rule ordIso_symmetric[OF bd_iterm_pre_ordIso])
  done

instantiation ivar :: var_iterm_pre begin
instance
  apply standard
    apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF card_ivar]])
    subgoal sorry
    (*apply (rule ordIso_ordLeq_trans[OF card_of_Field_natLeq])
    apply (rule ordLess_imp_ordLeq)
    apply (rule cardSuc_greater[OF natLeq_Card_order]) *)
   apply (rule regularCard_ordIso[OF ordIso_symmetric[OF card_ivar]])
    apply (simp add: Cinfinite_cardSuc natLeq_Card_order natLeq_cinfinite)
   apply (simp add: natLeq_Cinfinite regularCard_cardSuc)
  apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF card_ivar]])

  (* apply (metis Field_card_suc cardSuc_ordIso_card_suc card_order_card_suc Un_iff card_of_unique
    natLeq_card_order ordIso_symmetric ordIso_transitive ordLeq_ordLess_Un_ordIso) 
  done *)
  sorry
end

type_synonym itrm = "ivar iterm"

(* Some lighter notations: *)
abbreviation "VVr \<equiv> tvVVr_itvsubst"
lemmas VVr_def = tvVVr_itvsubst_def
abbreviation "isVVr \<equiv> tvisVVr_itvsubst"
lemmas isVVr_def = tvisVVr_itvsubst_def
abbreviation "IImsupp \<equiv> tvIImsupp_itvsubst"
lemmas IImsupp_def = tvIImsupp_itvsubst_def
abbreviation "SSupp \<equiv> tvSSupp_itvsubst"
lemmas SSupp_def = tvSSupp_itvsubst_def
abbreviation "FFVars \<equiv> FFVars_iterm"

abbreviation "rrename \<equiv> rrename_iterm"
(* *)

lemma FFVars_itvsubst[simp]:
"FFVars (itvsubst \<sigma> t) = (\<Union> {FFVars (\<sigma> x) | x . x \<in> FFVars t})"
sorry (* AtoDJ: This lemma was no longer available... *)

(*
lemma fsupp_le[simp]: 
"fsupp (\<sigma>::ivar\<Rightarrow>ivar) \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set|" 
by (simp add: finite_card_var fsupp_def supp_def)
*)

(* *)

(* Enabling some simplification rules: *)
lemmas iterm.tvsubst_VVr[simp] 
lemmas iterm.FVars_VVr[simp]
iterm.rrename_ids[simp] iterm.rrename_cong_ids[simp]
iterm.FFVars_rrenames[simp]

lemma singl_bound: "|{a}| <o |UNIV::ivar set|"
  by (simp add: finite_card_ivar)

lemma ls_UNIV_iff_finite: "|A| <o |UNIV::ivar set| \<longleftrightarrow> countable A"
using countable_iff_le_card_ivar by blast

lemma supp_id_update_le[simp,intro]:
"|supp (id(x := y))| <o |UNIV::ivar set|"
by (metis finite.emptyI finite_insert finite_ordLess_infinite2 imsupp_id_fun_upd imsupp_supp_bound infinite_ivar)
 
lemma IImsupp_VVr_empty[simp]: "IImsupp VVr = {}"
  unfolding IImsupp_def
  iterm.SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
  done

(* VVr is here the Var constructor: *)
lemma VVr_eq_Var[simp]: "VVr = iVar"
  unfolding VVr_def iVar_def comp_def
  tv\<eta>_iterm_itvsubst_def
  by (rule refl)

(* *)
(* Properties of term-for-variable substitution *)

lemma itvsubst_VVr_func[simp]: "itvsubst VVr t = t"
  apply (rule iterm.TT_plain_co_induct)
  subgoal for x
    apply (rule case_split[of "isVVr (iterm_ctor x)"])
     apply (unfold isVVr_def)[1]
     apply (erule exE)
    subgoal premises prems for a
      unfolding prems
      apply (rule iterm.tvsubst_VVr)
      apply (rule iterm.SSupp_VVr_bound)
        done
      apply (rule trans)
       apply (rule iterm.tvsubst_cctor_not_isVVr)
          apply (rule iterm.SSupp_VVr_bound)
      unfolding IImsupp_VVr_empty
         apply (rule Int_empty_right)
      unfolding noclash_iterm_def Int_Un_distrib Un_empty
        apply (rule conjI)
         apply (rule iffD2[OF disjoint_iff], rule allI, rule impI, assumption)
        apply (rule iffD2[OF disjoint_iff], rule allI, rule impI)
      unfolding UN_iff Set.bex_simps
        apply (rule ballI)
        apply assumption+
      apply (rule arg_cong[of _ _ iterm_ctor])
      apply (rule trans)
      apply (rule iterm_pre.map_cong)
                 apply (rule supp_id_bound bij_id)+
           apply (assumption | rule refl)+
      unfolding id_def[symmetric] iterm_pre.map_id
      apply (rule refl)
      done
    done

proposition rrename_simps[simp]:
  assumes "bij (f::ivar \<Rightarrow> ivar)" "|supp f| <o |UNIV::ivar set|"
  shows "rrename f (iVar a) = iVar (f a)"
    "rrename f (iApp e1 es2) = iApp (rrename f e1) (smap (rrename f) es2)"
    "rrename f (iAbs xs e) = iAbs (smap f xs) (rrename f e)"
  unfolding iVar_def iApp_def iAbs_def iterm.rrename_cctors[OF assms] map_iterm_pre_def comp_def
    Abs_iterm_pre_inverse[OF UNIV_I] map_sum_def sum.case map_prod_def prod.case id_def
    apply (rule refl)+
  done

thm iterm.strong_induct[of "\<lambda>\<rho>. A" "\<lambda>t \<rho>. P t", rule_format, no_vars]


lemma itrm_strong_induct[consumes 1, case_names iVar iApp iAbs]: 
"|A| <o |UNIV::ivar set|  
\<Longrightarrow>
(\<And>x. P (iVar (x::ivar))) 
\<Longrightarrow>
(\<And>t1 ts2. P t1 \<Longrightarrow> (\<And>z. z \<in> sset ts2 \<Longrightarrow> P z) \<Longrightarrow> P (iApp t1 ts2)) 
\<Longrightarrow> 
(\<And>xs t. sset xs \<inter> A = {} \<Longrightarrow> P t \<Longrightarrow> P (iAbs xs t)) 
\<Longrightarrow> 
P t"
apply(rule iterm.strong_induct[of "\<lambda>\<rho>. A" "\<lambda>t \<rho>. P t", rule_format])
by auto

lemma rrename_cong:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" and g: "bij g" "|supp g| <o |UNIV::ivar set|"
and eq: "(\<And>z. (z::ivar) \<in> FFVars P \<Longrightarrow> f z = g z)"
shows "rrename f P = rrename g P"
proof-
  have 0: "|supp f \<union> supp g| <o |UNIV::ivar set|" 
    using f(2) g(2) var_stream_class.Un_bound by blast
  show ?thesis using 0 eq apply(induct P rule: itrm_strong_induct)
    subgoal using f g by auto
    subgoal using f g by simp (metis stream.map_cong0)  
    subgoal using f g by simp (metis (no_types, opaque_lifting) Int_emptyD UnI1 UnI2 not_in_supp_alt 
                       stream.map_ident_strong) .
qed
 


proposition iApp_inject[simp]: "(iApp a b = iApp c d) = (a = c \<and> b = d)"
proof
  assume "iApp a b = iApp c d"
  then show "a = c \<and> b = d"
    unfolding iApp_def fun_eq_iff iterm.TT_injects0
      map_iterm_pre_def comp_def Abs_iterm_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
      Abs_iterm_pre_inject[OF UNIV_I UNIV_I]
    by auto
qed simp

proposition iVar_inject[simp]: "(iVar a = iVar b) = (a = b)"
  apply (rule iffI[rotated])
   apply (rule arg_cong[of _ _ iVar])
  apply assumption
  unfolding iVar_def iterm.TT_injects0 map_iterm_pre_def comp_def map_sum_def sum.case Abs_iterm_pre_inverse[OF UNIV_I]
  id_def Abs_iterm_pre_inject[OF UNIV_I UNIV_I] sum.inject
  apply (erule exE conjE)+
  apply assumption
  done

lemma iAbs_inject: "(iAbs xs e = iAbs xs' e') = (\<exists>f. bij f \<and> |supp (f::ivar \<Rightarrow> ivar)| <o |UNIV::ivar set|
  \<and> id_on (FFVars (iAbs xs e)) f \<and> smap f xs = xs' \<and> rrename f e = e')"
  unfolding iterm.set
  unfolding iAbs_def iterm.TT_injects0 map_iterm_pre_def comp_def Abs_iterm_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_iterm_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_iterm_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_iterm_pre_def
    Un_empty_right UN_single by auto

lemma bij_map_term_pre: "bij f \<Longrightarrow> |supp (f::ivar \<Rightarrow> ivar)| <o |UNIV::ivar set| \<Longrightarrow> bij (map_iterm_pre (id::ivar \<Rightarrow>ivar) f (rrename f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_iterm_pre id (inv f) (rrename (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule iterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 iterm.rrename_comp0s iterm.rrename_id0s
  apply (rule iterm_pre.map_id0)
  apply (rule trans)
   apply (rule iterm_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 iterm.rrename_comp0s iterm.rrename_id0s
  apply (rule iterm_pre.map_id0)
  done

lemma map_term_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::ivar \<Rightarrow> ivar)| <o |UNIV::ivar set| \<Longrightarrow> 
   inv (map_iterm_pre (id::_::var_iterm_pre \<Rightarrow> _) f (rrename f) id) = map_iterm_pre id (inv f) (rrename (inv f)) id"
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
  apply assumption
  apply (rule inv_unique_comp)
   apply (rule trans)
    apply (rule iterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
   defer
  apply (rule trans)
    apply (rule iterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 inv_o_simp2 iterm.rrename_comp0s iterm.rrename_id0s iterm_pre.map_id0
   apply (rule refl)+
  done

lemma Abs_set3: "iterm_ctor v = iAbs (xs::ivar stream) e \<Longrightarrow> 
 \<exists>xs' e'. iterm_ctor v = iAbs xs' e' \<and> sset xs' \<subseteq> set2_iterm_pre v \<and> e' \<in> set3_iterm_pre v"
  unfolding iAbs_def iterm.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_iterm_pre id f (rrename f) id"])
     apply (rule bij_map_term_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding iterm.rrename_id0s iterm_pre.map_id map_term_pre_inv_simp
    unfolding map_iterm_pre_def comp_def Abs_iterm_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_iterm_pre_def set3_iterm_pre_def comp_def Abs_iterm_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding iterm.FFVars_rrenames[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF iterm.rrename_bijs[OF bij_imp_bij_inv supp_inv_bound]]
  iterm.rrename_inv_simps[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding iterm.rrename_comps[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 iterm.rrename_ids
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+ 
  by auto .

lemma Abs_avoid: "|A::ivar set| <o |UNIV::ivar set| \<Longrightarrow> \<exists>xs' e'. iAbs xs e = iAbs xs' e' \<and> sset xs' \<inter> A = {}"
  apply (drule iterm.TT_fresh_nchotomys[of _ "iAbs xs e"])
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
  by auto

lemma Abs_rrename:
"bij (\<sigma>::ivar\<Rightarrow>ivar) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: ivar set| \<Longrightarrow>
 (\<And>a'. a' \<in> FFVars e - sset (as::ivar stream) \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> iAbs as e = iAbs (smap \<sigma> as) (rrename \<sigma> e)"
by (metis rrename_simps(3) iterm.rrename_cong_ids iterm.set(3))


(* Bound properties (needed as auxiliaries): *)

lemma SSupp_upd_bound:
  fixes f::"ivar \<Rightarrow> itrm" 
  shows "|SSupp (f (a:=t))| <o |UNIV::ivar set| \<longleftrightarrow> |SSupp f| <o |UNIV::ivar set|"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply singl_bound ordLeq_refl split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF iterm_pre.Un_bound], rotated]
      intro: card_of_mono1)  sorry


corollary SSupp_upd_VVr_bound[simp,intro!]: "|SSupp (VVr(a:=(t::itrm)))| <o |UNIV::ivar set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule iterm.SSupp_VVr_bound)
  done

lemma SSupp_upd_iVar_bound[simp,intro!]: "|SSupp (iVar(a:=(t::itrm)))| <o |UNIV::ivar set|"
using SSupp_upd_VVr_bound by auto

lemma supp_swap_bound[simp,intro!]: "|supp (id(x::ivar := xx, xx := x))| <o |UNIV:: ivar set|"
by (simp add: cinfinite_imp_infinite supp_swap_bound iterm.UNIV_cinfinite)

lemma SSupp_IImsupp_bound: "|SSupp \<sigma>| <o |UNIV:: ivar set| \<Longrightarrow> |IImsupp \<sigma>| <o |UNIV:: ivar set|"
unfolding IImsupp_def
by (simp add: var_ID_class.Un_bound iterm.set_bd_UNIV var_iterm_pre_class.UN_bound)

(* *)

lemma IImsupp_itvsubst_su:
assumes s[simp]: "|SSupp \<sigma>| <o  |UNIV:: ivar set|"
shows "IImsupp (itvsubst (\<sigma>::ivar\<Rightarrow>itrm) o \<tau>) \<subseteq> IImsupp \<sigma> \<union> IImsupp \<tau>"
unfolding IImsupp_def SSupp_def apply auto
by (metis s singletonD iterm.set(1) iterm.subst(1))

lemma IImsupp_itvsubst_su':
assumes s[simp]: "|SSupp \<sigma>| <o  |UNIV:: ivar set|"
shows "IImsupp (\<lambda>a. itvsubst (\<sigma>::ivar\<Rightarrow>itrm) (\<tau> a)) \<subseteq> IImsupp \<sigma> \<union> IImsupp \<tau>"
using IImsupp_itvsubst_su[OF assms] unfolding o_def .

lemma IImsupp_itvsubst_bound:
assumes s: "|SSupp \<sigma>| <o |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|IImsupp (itvsubst (\<sigma>::ivar\<Rightarrow>itrm) o \<tau>)| <o |UNIV:: ivar set|"
using IImsupp_itvsubst_su[OF s(1)] s
by (meson Un_bound SSupp_IImsupp_bound card_of_subset_bound)

lemma SSupp_itvsubst_bound:
assumes s: "|SSupp \<sigma>| <o |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|SSupp (itvsubst (\<sigma>::ivar\<Rightarrow>itrm) o \<tau>)| <o |UNIV:: ivar set|"
using IImsupp_itvsubst_bound[OF assms]
by (metis IImsupp_def card_of_subset_bound sup_ge1)

lemma SSupp_itvsubst_bound':
assumes s: "|SSupp \<sigma>| <o |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|SSupp (\<lambda>a. itvsubst (\<sigma>::ivar\<Rightarrow>itrm) (\<tau> a))| <o |UNIV:: ivar set|"
using SSupp_itvsubst_bound[OF assms] unfolding o_def .

(* *)

lemma IImsupp_rrename_su:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|"
shows "IImsupp (rrename (\<sigma>::ivar\<Rightarrow>ivar) o \<tau>) \<subseteq> imsupp \<sigma> \<union> IImsupp \<tau>"
unfolding IImsupp_def imsupp_def supp_def SSupp_def by force

lemma IImsupp_rrename_su':
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|"
shows "IImsupp (\<lambda>a. rrename (\<sigma>::ivar\<Rightarrow>ivar) (\<tau> a)) \<subseteq> imsupp \<sigma> \<union> IImsupp \<tau>"
using IImsupp_rrename_su[OF assms] unfolding o_def .

lemma IImsupp_rrename_bound:
assumes s: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|IImsupp (rrename (\<sigma>::ivar\<Rightarrow>ivar) o \<tau>)| <o |UNIV:: ivar set|"
using IImsupp_rrename_su[OF s(1,2)] s
by (metis SSupp_IImsupp_bound finite_Un finite_iff_le_card_ivar finite_subset imsupp_supp_bound infinite_ivar)

lemma SSupp_rrename_bound:
assumes s: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|SSupp (rrename (\<sigma>::ivar\<Rightarrow>ivar) o \<tau>)| <o |UNIV:: ivar set|"
using IImsupp_rrename_bound[OF assms]
by (metis IImsupp_def card_of_subset_bound sup_ge1)

lemma SSupp_rrename_bound':
assumes s: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|SSupp (\<lambda>a. rrename (\<sigma>::ivar\<Rightarrow>ivar) (\<tau> a))| <o |UNIV:: ivar set|"
using SSupp_rrename_bound[OF assms] unfolding o_def .

(* *)
lemma SSupp_update_rrename_bound:
"|SSupp (iVar(\<sigma> (x::ivar) := rrename \<sigma> e))| <o |UNIV::ivar set|"
using SSupp_upd_iVar_bound .

lemma IImsupp_rrename_update_su:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "IImsupp (rrename \<sigma> \<circ> iVar(x := e)) \<subseteq>
       imsupp \<sigma> \<union> {x} \<union> FFVars_iterm e"
unfolding IImsupp_def SSupp_def imsupp_def supp_def by (auto split: if_splits)

lemma IImsupp_rrename_update_bound:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "|IImsupp (rrename \<sigma> \<circ> iVar(x := e))| <o |UNIV::ivar set|"
using IImsupp_rrename_update_su[OF assms]
by (meson Un_bound card_of_subset_bound imsupp_supp_bound infinite_ivar s(2) singl_bound iterm.set_bd_UNIV)

lemma SSupp_rrename_update_bound:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "|SSupp (rrename \<sigma> \<circ> iVar(x := e))| <o |UNIV::ivar set|"
using IImsupp_rrename_update_bound[OF assms] unfolding IImsupp_def  apply auto
HERE
(* 
  by (smetis (mono_tags) IImsupp_def finite_Un finite_iff_le_card_var)

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

lemma itvsubst_comp:
assumes s[simp]: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "itvsubst (\<sigma>::var\<Rightarrow>trm) (itvsubst \<tau> e) = itvsubst (itvsubst \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_itvsubst_bound'[OF s, simp]
  show ?thesis
  apply(induct e rule: term.fresh_induct[where A = "IImsupp \<sigma> \<union> IImsupp \<tau>"])
    subgoal using Un_bound[OF s]
      using var_ID_class.Un_bound SSupp_IImsupp_bound s(1) s(2) by blast
    subgoal by simp
    subgoal by simp
    subgoal for x t apply(subgoal_tac "x \<notin> IImsupp (\<lambda>a. itvsubst \<sigma> (\<tau> a))")
      subgoal by simp
      subgoal using IImsupp_itvsubst_su'[OF s(1)] by blast . .
qed

lemma rrename_itvsubst_comp:
assumes b[simp]: "bij (\<sigma>::var\<Rightarrow>var)" and s[simp]: "|supp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "rrename \<sigma> (itvsubst \<tau> e) = itvsubst (rrename \<sigma> \<circ> \<tau>) e"
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

(* Equivariance of unary substitution: *)

lemma itvsubst_rrename_comp[simp]:
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "itvsubst (rrename \<sigma> \<circ> Var(x := e2)) e1 = itvsubst (Var(\<sigma> x := rrename \<sigma> e2)) (rrename \<sigma> e1)"
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
lemma itvsubst_Var_rrename:
assumes xx: "xx \<notin> FFVars_term e1 - {x}"
shows "itvsubst (Var((x::var) := e2)) e1 = itvsubst (Var(xx := e2)) (rrename (id(x := xx, xx := x)) e1)"
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
"swap (Abs v t) (y::var) x = Abs (sw v y x) (swap t y x)"
by (auto simp: sw_def)

lemma FFVars_swap[simp]: "FFVars (swap t y x) =
 (\<lambda>u. sw u x y) ` (FFVars t)"
apply(subst term.FFVars_rrenames) by (auto simp: sw_def)

lemma FFVars_swap'[simp]: "{x::var,y} \<inter> FFVars t = {} \<Longrightarrow> swap t x y = t"
apply(rule term.rrename_cong_ids) by auto

(* *)

lemma Abs_inject_swap: "Abs v t = Abs v' t' \<longleftrightarrow>
  (v' \<notin> FFVars t \<or> v' = v) \<and> swap t v' v = t'"
unfolding Abs_inject apply(rule iffI)
  subgoal unfolding id_on_def apply auto
  apply(rule rrename_cong) by auto
  subgoal apply clarsimp
  apply(rule exI[of _ "id(v':=v,v:=v')"]) unfolding id_on_def by auto .

lemma Abs_inject_swap': "Abs v t = Abs v' t' \<longleftrightarrow>
  (\<exists>z. (z \<notin> FFVars t \<or> z = v) \<and> (z \<notin> FFVars t' \<or> z = v') \<and>
       swap t z v = swap t' z v')"
unfolding Abs_inject_swap apply(rule iffI)
  subgoal apply clarsimp apply(rule exI[of _ v']) by auto
  subgoal by (smt (verit, del_insts) Abs_inject_swap)    .

lemma Abs_refresh': "v' \<notin> FFVars t \<or> v' = v \<Longrightarrow>
   Abs v t = Abs v' (swap t v' v)"
using Abs_inject_swap by auto

lemma Abs_refresh:
"xx \<notin> FFVars t \<or> xx = x \<Longrightarrow> Abs x t = Abs xx (swap t x xx)"
by (metis Abs_inject_swap fun_upd_twist)

(* *)

lemma FFVars_usub[simp]: "FFVars (usub t y x) =
 (if x \<in> FFVars t then FFVars t - {x} \<union> {y} else FFVars t)"
apply(subst term.set_map) by auto

lemma usub_simps_free[simp]: "\<And>y x. usub (Var z) (y::var) x = Var (sb z y x)"
"\<And>y x t s. usub (App t s) (y::var) x = App (usub t y x) (usub s y x)"
by (auto simp: sb_def)

lemma usub_Abs[simp]:
"v \<notin> {x,y} \<Longrightarrow> usub (Abs v t) (y::var) x = Abs v (usub t y x)"
apply(subst term.map)
  subgoal by auto
  subgoal by (auto simp: imsupp_def supp_def)
  subgoal by auto .

lemmas usub_simps = usub_simps_free usub_Abs

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




thm term.rrename_comps

typ trm

term FFVars
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

end