(* Types for System F with SubTypeing  *)
theory SystemFSub_Types
  imports "Binders.MRBNF_Recursor"
    "Binders.Generic_Strong_Rule_Induction"
    "Prelim.Curry_LFP"
    "Prelim.FixedCountableVars"
    "Labeled_FSet"
begin

declare bij_swap[simp]
declare supp_id_bound[simp]

(*type_synonym label = nat*)

declare [[mrbnf_internals]]
binder_datatype 'var "Type" =
    TyVar 'var
  | Top
  | Fun "'var Type" "'var Type"
  | Forall X::'var "'var Type" T::"'var Type" binds X in T

declare supp_swap_bound[OF cinfinite_imp_infinite[OF Type.UNIV_cinfinite], simp]
declare Type.rrename_ids[simp] Type.rrename_id0s[simp]

lemma rrename_Type_simps[simp]:
  fixes f::"'a::var_Type_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
    "rrename_Type f (TyVar X) = TyVar (f X)"
    "rrename_Type f Top = Top"
    "rrename_Type f (Fun t1 t2) = Fun (rrename_Type f t1) (rrename_Type f t2)"
    "rrename_Type f (Forall Y T1 T2) = Forall (f Y) (rrename_Type f T1) (rrename_Type f T2)"
     apply (unfold TyVar_def Top_def Fun_def Forall_def)
     apply (rule trans)
      apply (rule Type.rrename_cctors)
       apply (rule assms)+
     defer
     apply (rule trans)
      apply (rule Type.rrename_cctors)
       apply (rule assms)+
     defer
     apply (rule trans)
      apply (rule Type.rrename_cctors)
       apply (rule assms)+
     defer
     apply (rule trans)
      apply (rule Type.rrename_cctors)
       apply (rule assms)+
     defer
     apply (unfold map_Type_pre_def comp_def Abs_Type_pre_inverse[OF UNIV_I] map_sum.simps
        map_prod_simp id_def
      )
     apply (rule refl)+
  done

lemma Type_inject:
  "TyVar X = TyVar Y \<longleftrightarrow> X = Y"
  "Fun T1 T2 = Fun R1 R2 \<longleftrightarrow> T1 = R1 \<and> T2 = R2"
  "Forall X T1 T2 = Forall Y R1 R2 \<longleftrightarrow> 
   T1 = R1 \<and> (\<exists>f. bij (f::'a::var_Type_pre \<Rightarrow> 'a) \<and> 
   |supp f| <o |UNIV::'a set| \<and> id_on (FFVars_Type T2 - {X}) f \<and> f X = Y \<and> rrename_Type f T2 = R2)"
    apply (unfold TyVar_def Fun_def Forall_def Type.TT_injects0
      set3_Type_pre_def comp_def Abs_Type_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_Type_pre_def
      prod.map_id set2_Type_pre_def prod_set_simps prod.set_map UN_single Abs_Type_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp
    )
  by auto
declare Type_inject(1,2)[simp]

corollary Forall_inject_same[simp]: "Forall X T1 T2 = Forall X S1 S2 \<longleftrightarrow> T1 = S1 \<and> T2 = S2"
  using Type_inject(3) Type.rrename_cong_ids
  by (metis (no_types, lifting) Diff_empty Diff_insert0 id_on_insert insert_Diff)

lemma Forall_rrename:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|" shows "
 (\<And>Y. Y\<in>FFVars_Type T2 - {X::'a::var_Type_pre} \<Longrightarrow> \<sigma> Y = Y) \<Longrightarrow> Forall X T1 T2 = Forall (\<sigma> X) T1 (rrename_Type \<sigma> T2)"
  apply (unfold Forall_def)
  apply (unfold Type.TT_injects0)
  apply (unfold set3_Type_pre_def set2_Type_pre_def comp_def Abs_Type_pre_inverse[OF UNIV_I] map_sum.simps
    map_prod_simp sum_set_simps prod_set_simps cSup_singleton Un_empty_left Un_empty_right
    Union_empty image_insert image_empty map_Type_pre_def id_def)
  apply (rule exI[of _ \<sigma>])
  apply (rule conjI assms)+
   apply (unfold id_on_def atomize_all atomize_imp)[1]
   apply (rule impI)
   apply assumption
  apply (rule refl)
  done

lemma Forall_swap: "y \<notin> FFVars_Type T2 - {x} \<Longrightarrow> Forall (x::'a::var_Type_pre) T1 T2 = Forall y T1 (rrename_Type (id(x:=y,y:=x)) T2)"
  apply (rule trans)
   apply (rule Forall_rrename)
     apply (rule bij_swap[of x y])
    apply (rule supp_swap_bound)
    apply (rule cinfinite_imp_infinite[OF Type.UNIV_cinfinite])
  by auto

(* Monomorphising: *)
instance var :: var_Type_pre apply standard
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)

type_synonym type = "var Type"
type_synonym \<Gamma>\<^sub>\<tau> = "(var \<times> type) list"

definition map_context :: "(var \<Rightarrow> var) \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>" where
  "map_context f \<equiv> map (map_prod f (rrename_Type f))"

abbreviation FFVars_ctxt :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var set" where
  "FFVars_ctxt xs \<equiv> \<Union>(FFVars_Type ` snd ` set xs)"
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
  using assms by (auto simp: Type.rrename_comps)

lemmas map_context_comp = trans[OF comp_apply[symmetric] fun_cong[OF map_context_comp0]]
declare map_context_comp[simp]

lemma context_dom_set[simp]:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "dom (map_context f xs) = f ` dom xs"
  unfolding map_context_def by force
lemma set_bd_UNIV: "|set xs| <o |UNIV::var set|"
  apply (rule ordLess_ordLeq_trans)
    apply (tactic \<open>resolve_tac @{context} (BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name list}))) 1\<close>)
  apply (rule var_Type_pre_class.large)
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
  using assms by (fastforce intro!: Type.rrename_cong_ids)+

lemma ls_UNIV_iff_finite: "|A| <o |UNIV::var set| \<longleftrightarrow> finite A"
using finite_iff_le_card_var by blast

lemma rrename_swap_FFvars[simp]: "X \<notin> FFVars_Type T \<Longrightarrow> Y \<notin> FFVars_Type T \<Longrightarrow>
  rrename_Type (id(X := Y, Y := X)) T = T"
apply(rule Type.rrename_cong_ids) by auto

lemma map_context_swap_FFVars[simp]:
"\<forall>k\<in>set \<Gamma>. X \<noteq> fst k \<and> X \<notin> FFVars_Type (snd k) \<and>
           Y \<noteq> fst k \<and> Y \<notin> FFVars_Type (snd k) \<Longrightarrow>
    map_context (id(X := Y, Y := X)) \<Gamma> = \<Gamma>"
  unfolding map_context_def apply(rule map_idI) by auto

lemma isPerm_swap: "isPerm (id(X := Y, Y := X))"
  unfolding isPerm_def by (auto simp: supp_swap_bound infinite_UNIV)

notation Fun (infixr "\<rightarrow>" 65)
notation Forall ("\<forall> _ <: _ . _" [62, 62, 62] 70)


end
