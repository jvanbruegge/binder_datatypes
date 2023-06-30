theory POPLmark_1A
  imports "../MRBNF_Recursor"
    "../../DAList" "../Instantiation_Infrastructure/FixedCountableVars"
    "../Instantiation_Infrastructure/Curry_LFP"
    "../Generic_Barendregt_Enhanced_Rule_Induction"
begin

declare bij_swap[simp]
declare supp_id_bound[simp]

ML \<open>
val ctors = [
  (("TyVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("Top", (NONE : mixfix option)), []),
  (("Fun", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Forall", NONE), [@{typ 'bvar}, @{typ 'rec}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "typ"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst_typ},
  tvsubst_b = @{binding tvsubst_typ}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

instance var :: var_typ_pre apply standard
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)
instance var :: var_dalist apply standard
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)

declare supp_swap_bound[OF cinfinite_imp_infinite[OF typ.UNIV_cinfinite], simp]
declare typ.rrename_ids[simp] typ.rrename_id0s[simp]

lemma rrename_typ_simps[simp]:
  fixes f::"'a::var_typ_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
    "rrename_typ f (TyVar a) = TyVar (f a)"
    "rrename_typ f Top = Top"
    "rrename_typ f (Fun t1 t2) = Fun (rrename_typ f t1) (rrename_typ f t2)"
    "rrename_typ f (Forall x T1 T2) = Forall (f x) (rrename_typ f T1) (rrename_typ f T2)"
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

type_synonym type = "var typ"

abbreviation pre_dom :: "(var \<times> type) list \<Rightarrow> var set" where "pre_dom xs \<equiv> fst ` set xs"

fun well_formed :: "(var \<times> type) list \<Rightarrow> bool" where
  "well_formed [] \<longleftrightarrow> True"
| "well_formed ((x, t)#xs) \<longleftrightarrow> x \<notin> pre_dom xs \<and> FFVars_typ t \<subseteq> pre_dom xs \<and> well_formed xs"

typedef \<Gamma>\<^sub>\<tau> = "{ xs::(var \<times> type) list. well_formed xs }"
  by (rule exI[of _ "[]"]) simp

setup_lifting type_definition_\<Gamma>\<^sub>\<tau>

lift_definition map_context :: "(var \<Rightarrow> var) \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>"
  is "\<lambda>f xs. if bij f \<and> |supp f| <o |UNIV::var set| then map (map_prod f (rrename_typ f)) xs else []"
  subgoal for f xs
    apply (induction xs)
     apply (auto simp: rev_image_eqI typ.FFVars_rrenames)
    by (metis Product_Type.fst_comp_map_prod image_comp image_eqI subset_eq)
  done
lift_definition dom :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var set" is "pre_dom" .
lift_definition pairs :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> (var \<times> type) set" is "set" .

lift_definition extend :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau>" ("_ , _ <: _" [57,57,57] 62)
  is "\<lambda>\<Gamma> x T. if x \<notin> pre_dom \<Gamma> \<and> FFVars_typ T \<subseteq> pre_dom \<Gamma> then (x, T)#\<Gamma> else \<Gamma>"
  by auto
lift_definition concat :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>" ("_, _" [65,65] 70)
  is "\<lambda>xs ys. if pre_dom xs \<inter> pre_dom ys = {} then ys @ xs else []"
  subgoal for xs ys
    apply auto
    apply (induction ys)
     apply auto
      apply (metis fst_conv image_iff)
    apply (metis fst_conv image_iff)
    by auto
  done
lift_definition empty_context :: "\<Gamma>\<^sub>\<tau>" ("\<emptyset>") is "[]" by simp

lemma well_formed_dom: "well_formed xs \<Longrightarrow> T \<in> snd ` set xs \<Longrightarrow> FFVars_typ T \<subseteq> pre_dom xs"
proof (induction xs)
  case (Cons a xs)
  then show ?case
    apply (cases "T = snd a")
     apply (metis dual_order.trans image_mono prod.exhaust_sel set_subset_Cons well_formed.simps(2))
    apply simp
    apply (rule subset_insertI2)
    by (metis prod.exhaust_sel well_formed.simps(2))
qed simp

lemma map_context_id[simp]: "map_context id = id"
  by (rule ext, transfer, auto)
lemma map_context_comp0[simp]:
  assumes "bij f" "|supp f| <o |UNIV::var set|" "bij g" "|supp g| <o |UNIV::var set|"
  shows "map_context f \<circ> map_context g = map_context (f \<circ> g)"
  apply (rule ext)
  using assms apply transfer
  by (auto simp: supp_comp_bound infinite_var typ.rrename_comps)
lemmas map_context_comp = trans[OF comp_apply[symmetric] fun_cong[OF map_context_comp0]]
declare map_context_comp[simp]
lemma context_dom_set[simp]:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "dom (map_context f xs) = f ` dom xs"
  using assms apply transfer apply auto
  apply (metis fst_conv imageI)
  by (metis fst_conv fst_map_prod imageI)
lemma context_set_bd_UNIV[simp]: "|dom xs| <o |UNIV::var set|"
  apply transfer
   apply (rule ordLeq_ordLess_trans[OF card_of_image])
   apply (rule ordLess_ordLeq_trans)
    apply (tactic \<open>resolve_tac @{context} (BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name list}))) 1\<close>)
   apply (rule var_typ_pre_class.large)
  done
lemma map_context_cong_id:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
    and "\<And>a. a \<in> dom xs \<Longrightarrow> f a = a"
  shows "map_context f xs = xs"
  using assms apply transfer
  apply auto
  apply (rule trans)
   apply (rule list.map_cong)
    apply (rule refl)
   apply (rule prod.map_cong[of _ _ _ "\<lambda>x. x"])
     apply (rule refl)
    apply (simp add: fsts.simps)
   apply (rule typ.rrename_cong_ids)
     apply assumption+
  apply (metis imageI in_mono snds.cases well_formed_dom)
  apply simp
  done

declare [[inductive_internals]]

notation Fun (infixr "\<rightarrow>" 65)
notation Forall ("\<forall> _ <: _ . _" [62, 62, 62] 70)

abbreviation in_context :: "var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ <: _ \<in> _" [55,55,55] 60) where
  "x <: t \<in> \<Gamma> \<equiv> (x, t) \<in> pairs \<Gamma>"
abbreviation well_scoped :: "type \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ closed'_in _" [55, 55] 60) where
  "well_scoped S \<Gamma> \<equiv> FFVars_typ S \<subseteq> dom \<Gamma>"

inductive Ty :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [55,55,55] 60) where
  SA_Top: "S closed_in \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_Refl_TVar: "TyVar x closed_in \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: TyVar x"
| SA_Trans_TVar: "\<lbrakk> x<:U \<in> \<Gamma> ; \<Gamma> \<turnstile> U <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: T"
| SA_Arrow: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_All: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma>, x<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 ; x \<notin> dom \<Gamma> ; T\<^sub>1 closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<forall>x<:S\<^sub>1. S\<^sub>2 <: \<forall>x<:T\<^sub>1 .T\<^sub>2"

lemma pairs_dom: "dom \<Gamma> = fst ` pairs \<Gamma>"
  by transfer (rule refl)
lemma dom_extend[simp]: "x \<notin> dom \<Gamma> \<Longrightarrow> T closed_in \<Gamma> \<Longrightarrow> dom (\<Gamma>, x <: T) = dom \<Gamma> \<union> {x}"
  by transfer auto

lemma well_scoped[intro]:
  assumes "\<Gamma> \<turnstile> S <: T"
  shows "S closed_in \<Gamma>" "T closed_in \<Gamma>"
using assms proof (induction \<Gamma> S T rule: Ty.induct)
  case (SA_Trans_TVar x U \<Gamma> T) {
    case 1 then show ?case using SA_Trans_TVar
      by (metis fst_conv imageI pairs_dom singletonD subsetI typ.set(1))
  next
    case 2 then show ?case by (simp add: SA_Trans_TVar)
  }
qed auto

thm Ty_def
declare Ty.intros[intro]

(* instantiating the induction locale *)
interpretation Small where dummy = "undefined :: var"
apply standard
  apply (simp add: infinite_var)
  using var_typ_pre_class.regular by blast

type_synonym T = "\<Gamma>\<^sub>\<tau> \<times> type \<times> type"
type_synonym V = "var list"

definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where
  "Tmap f \<equiv> map_prod (map_context f) (map_prod (rrename_typ f) (rrename_typ f))"
fun Tfvars :: "T \<Rightarrow> var set" where
  "Tfvars (\<Gamma>, T\<^sub>1, T\<^sub>2) = dom \<Gamma> \<union> FFVars_typ T\<^sub>1 \<union> FFVars_typ T\<^sub>2"

definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where
  "Vmap \<equiv> map"
fun Vfvars :: "V \<Rightarrow> var set" where
  "Vfvars v = set v"

interpretation Components where dummy = "undefined :: var" and
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars
apply standard unfolding ssbij_def Tmap_def Vmap_def
  using small_Un small_def typ.card_of_FFVars_bounds
         apply (auto simp: typ.FFVars_rrenames map_prod.comp dalist.set_map dalist.map_comp typ.rrename_comp0s inf_A)
    apply (rule var_typ_pre_class.Un_bound var_typ_pre_class.UN_bound
        typ.card_of_FFVars_bounds dalist.set_bd[THEN ordLess_ordLeq_trans[OF _ var_typ_pre_class.large]])+
  by (auto simp: map_context_cong_id typ.rrename_cong_ids)

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> T \<Rightarrow> bool" where
  "G \<equiv> \<lambda>R v t.
    (v = [] \<and> snd (snd t) = Top \<and> fst (snd t) closed_in fst t)
  \<or> (\<exists>x. v = [] \<and> fst (snd t) = TyVar x \<and> fst (snd t) = snd (snd t) \<and> fst (snd t) closed_in fst t)
  \<or> (\<exists>x U \<Gamma> T. v = [] \<and> fst t = \<Gamma> \<and> fst (snd t) = TyVar x \<and> snd (snd t) = T \<and> x <: U \<in> \<Gamma> \<and> R (\<Gamma>, U, T))
  \<or> (\<exists>\<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2. v = [] \<and> fst t = \<Gamma> \<and> fst (snd t) = (S\<^sub>1 \<rightarrow> S\<^sub>2) \<and> snd (snd t) = (T\<^sub>1 \<rightarrow> T\<^sub>2) \<and> R (\<Gamma>, T\<^sub>1, S\<^sub>1) \<and> R (\<Gamma>, S\<^sub>2, T\<^sub>2))
  \<or> (\<exists>\<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2. v = [x] \<and> fst t = \<Gamma> \<and> fst (snd t) = (\<forall>x<:S\<^sub>1. S\<^sub>2) \<and> snd (snd t) = (\<forall>x<:T\<^sub>1. T\<^sub>2) \<and> R (\<Gamma>, T\<^sub>1, S\<^sub>1) \<and> R (\<Gamma>,x<:T\<^sub>1, S\<^sub>2, T\<^sub>2) \<and> x \<notin> dom \<Gamma> \<and> T\<^sub>1 closed_in \<Gamma>)
  "

lemma GG_mono: "R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
  unfolding G_def by fastforce

lemma in_context_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "x <: T \<in> \<Gamma> \<Longrightarrow> f x <: rrename_typ f T \<in> map_context f \<Gamma>"
  using assms by transfer (auto simp: inj_on_def)

lemma extend_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "map_context f (\<Gamma>,x<:T) = map_context f \<Gamma>,f x <: rrename_typ f T"
  using assms apply transfer apply (auto simp: typ.FFVars_rrenames)
     apply (metis fst_conv image_iff)
    apply (metis Product_Type.fst_comp_map_prod imageI image_comp subset_eq)
   apply (metis fst_conv image_iff map_prod_imageI)
  by (smt (verit, best) bij_not_equal_iff fst_conv image_iff image_subset_iff prod_fun_imageE)

lemma closed_in_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "S closed_in \<Gamma> \<Longrightarrow> rrename_typ f S closed_in map_context f \<Gamma>"
  using assms apply transfer
  apply (auto simp: typ.FFVars_rrenames)
  by (metis Product_Type.fst_comp_map_prod imageI image_comp subset_eq)

lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
  unfolding G_def
  apply (elim disjE)
  subgoal
    apply (rule disjI1)
    apply (cases t)
    unfolding ssbij_def Tmap_def Vmap_def using closed_in_eqvt by simp
  subgoal
    apply (rule disjI2, rule disjI1)
    apply (erule exE)
    apply (elim conjE)
    subgoal for x
      apply (cases t)
      unfolding ssbij_def Tmap_def Vmap_def by auto
    done
  subgoal
    apply (rule disjI2, rule disjI2, rule disjI1)
    apply (elim exE conjE)
    subgoal for x U \<Gamma> T
      apply (rule exI)
      apply (rule exI[of _ "rrename_typ \<sigma> U"])
      apply (rule exI[of _ "map_context \<sigma> \<Gamma>"])
      apply (rule exI[of _ "rrename_typ \<sigma> T"])
      apply (cases t)
      unfolding ssbij_def Tmap_def Vmap_def
      by (auto simp: in_context_eqvt supp_inv_bound typ.rrename_comps typ.rrename_comp0s)
    done
  subgoal
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
    apply (elim exE conjE)
    subgoal for \<Gamma> T1 S1 S2 T2
      apply (rule exI[of _ "map_context \<sigma> \<Gamma>"])
      apply (rule exI[of _ "rrename_typ \<sigma> T1"])
      apply (rule exI[of _ "rrename_typ \<sigma> S1"])
      apply (rule exI[of _ "rrename_typ \<sigma> S2"])
      apply (rule exI[of _ "rrename_typ \<sigma> T2"])
      apply (cases t) unfolding ssbij_def Tmap_def Vmap_def
      by (auto simp: in_context_eqvt dalist.map_comp supp_inv_bound
          typ.rrename_comps typ.rrename_comp0s dalist.map_id)
    done
  apply (rule disjI2)+
  apply (elim exE conjE)
  subgoal for \<Gamma> T1 S1 x S2 T2
          apply (rule exI[of _ "map_context \<sigma> \<Gamma>"])
      apply (rule exI[of _ "rrename_typ \<sigma> T1"])
    apply (rule exI[of _ "rrename_typ \<sigma> S1"])
    apply (rule exI)
      apply (rule exI[of _ "rrename_typ \<sigma> S2"])
    apply (rule exI[of _ "rrename_typ \<sigma> T2"])
    apply (cases t) unfolding ssbij_def Tmap_def Vmap_def
    apply (auto simp: in_context_eqvt dalist.map_comp supp_inv_bound typ.FFVars_rrenames
          typ.rrename_comps typ.rrename_comp0s dalist.map_id extend_eqvt dalist.set_map
      )
    done
  done

lemma fresh: "\<exists>xx. xx \<notin> Tfvars t"
  by (metis emp_bound equals0D imageI inf.commute inf_absorb2 small_Tfvars small_def small_ssbij subsetI)

lemma Forall_rrename:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|" shows "
 (\<And>a'. a'\<in>FFVars_typ T2 - {x::'a::var_typ_pre} \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> Forall x T1 T2 = Forall (\<sigma> x) T1 (rrename_typ \<sigma> T2)"
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

lemma swap_idemp[simp]: "id(x := x) = id" by auto
lemma swap_left: "(id(x := xx, xx := x)) x = xx" by simp

lemma GG_fresh:
  "(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> G R v t \<Longrightarrow>
  \<exists>w. Vfvars w \<inter> Tfvars t = {} \<and> G R w t"
  using fresh[of t] unfolding G_def Tmap_def Vmap_def apply safe
  subgoal by (rule exI[of _ "[]"]) auto
  subgoal by (rule exI[of _ "[]"]) auto
  subgoal by (rule exI[of _ "[]"]) auto
  subgoal by (rule exI[of _ "[]"]) fastforce
  subgoal for xx \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2
    apply (rule exI[of _ "[xx]"])
    apply (rule conjI)
    subgoal by auto
    apply (rule disjI2)+
    apply (rule exI[of _ "fst t"])
  apply (rule exI[of _ "T\<^sub>1"])
    apply (rule exI[of _ "S\<^sub>1"])
    apply (rule exI[of _ "xx"])
    apply (rule exI[of _ "rrename_typ (id(x:=xx,xx:=x)) S\<^sub>2"])
    apply (rule exI[of _ "rrename_typ (id(x:=xx,xx:=x)) T\<^sub>2"])
    apply (cases t) apply simp
    apply (intro conjI)
    subgoal apply (subst Forall_rrename[of "id(x:=xx,xx:=x)"]) by auto
    subgoal
      apply (elim conjE)
        apply (subst Forall_rrename[of "id(x:=xx,xx:=x)"])
      by auto
    apply (rule iffD2[OF arg_cong[of _ _ R]])
     apply (rule arg_cong[of _ _ "\<lambda>x::\<Gamma>\<^sub>\<tau>. (x, _::type, _::type)"])
     defer
     apply (elim allE)
     apply (erule impE)
      prefer 2
      apply assumption
     apply (rule conjI)
      apply (simp add: ssbij_def)
      apply assumption
    apply (subst extend_eqvt)
      apply (rule bij_swap)
     apply (rule supp_swap_bound)
     apply (rule infinite_var)
    apply (rule arg_cong3[of _ _ _ _ _ _ extend])
      apply (metis Prelim.bij_swap fun_upd_apply id_apply infinite_var map_context_cong_id supp_swap_bound)
     apply simp
    by (auto intro!: typ.rrename_cong_ids[symmetric])
  done

interpretation Induct where dummy = "undefined :: var"
  and Tmap = Tmap and Tfvars = Tfvars and Vmap = Vmap and Vfvars = Vfvars and G = G
  apply standard
  using GG_mono GG_equiv GG_fresh by auto
print_theorems

lemma Ty_I: "Ty \<Gamma> T1 T2 = I (\<Gamma>, T1, T2)"
  unfolding Ty_def I_def lfp_curry3 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
  unfolding fun_eq_iff G_def apply safe
           apply auto
  by blast+

corollary Ty_strong_induct[consumes 1, case_names Bound SA_Top SA_Refl_TVar SA_Trans_TVar SA_Arrow SA_All]:
  "\<Gamma> \<turnstile> S <: T \<Longrightarrow>
  \<forall>\<rho>. |K \<rho>| <o |UNIV::var set| \<Longrightarrow>
  (\<And>\<Gamma> S \<rho>. S closed_in \<Gamma> \<Longrightarrow> P \<Gamma> S Top \<rho>) \<Longrightarrow>
  (\<And>\<Gamma> x \<rho>. TyVar x closed_in \<Gamma> \<Longrightarrow> P \<Gamma> (TyVar x) (TyVar x) \<rho>) \<Longrightarrow>
  (\<And>x U \<Gamma> T \<rho>. x <: U \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> U <: T \<Longrightarrow> \<forall>\<rho>. P \<Gamma> U T \<rho> \<Longrightarrow> P \<Gamma> (TyVar x) T \<rho>) \<Longrightarrow>
  (\<And>\<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 \<rho>. \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> T\<^sub>1 S\<^sub>1 \<rho> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> S\<^sub>2 T\<^sub>2 \<rho> \<Longrightarrow> P \<Gamma> (S\<^sub>1 \<rightarrow> S\<^sub>2) (T\<^sub>1 \<rightarrow> T\<^sub>2) \<rho>) \<Longrightarrow>
  (\<And>\<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 \<rho>. x \<notin> K \<rho> \<Longrightarrow> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> T\<^sub>1 S\<^sub>1 \<rho> \<Longrightarrow> \<Gamma> , x <: T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow>
    \<forall>\<rho>. P (\<Gamma> , x <: T\<^sub>1) S\<^sub>2 T\<^sub>2 \<rho> \<Longrightarrow> x \<notin> dom \<Gamma> \<Longrightarrow> T\<^sub>1 closed_in \<Gamma> \<Longrightarrow> P \<Gamma> (\<forall> x <: S\<^sub>1 . S\<^sub>2) (\<forall> x <: T\<^sub>1 . T\<^sub>2) \<rho>) \<Longrightarrow>
 \<forall>\<rho>. P \<Gamma> S T \<rho>"
  unfolding Ty_I
  apply (rule allI)
  subgoal for \<rho>
    apply (subgoal_tac "case (\<Gamma>, S, T) of (\<Gamma>, S, T) \<Rightarrow> P \<Gamma> S T \<rho>")
    subgoal by auto
    subgoal apply (rule BE_induct[where R="\<lambda>p (\<Gamma>,S,T). P \<Gamma> S T p" and Pfvars = K])
        apply (unfold small_def)[1]
        apply (erule allE)
        apply assumption+
      unfolding G_def by (auto split: if_splits)
    done
  done

(********************* Actual formalization ************************)

lemma Ty_refl: "T closed_in \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> T <: T"
  by (binder_induction T arbitrary: \<Gamma> avoiding: "dom \<Gamma>" rule: typ.strong_induct)
     (auto simp: Diff_single_insert SA_All)

lemma pairs_extend[simp]: "x \<notin> dom \<Gamma> \<Longrightarrow> T closed_in \<Gamma> \<Longrightarrow> pairs (\<Gamma>, x <: T) = pairs \<Gamma> \<union> {(x, T)}"
  by transfer auto

lemma Ty_permute: "\<lbrakk> \<Gamma> \<turnstile> S <: T ; pairs \<Gamma> = pairs \<Delta> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> S <: T"
proof (binder_induction \<Gamma> S T arbitrary: \<Delta> avoiding: "dom \<Delta>" rule: Ty_strong_induct)
  case (Bound \<Delta>)
  then show ?case by (rule context_set_bd_UNIV)
next
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 \<Delta>)
  then have "pairs (\<Gamma>, x <: T\<^sub>1) = pairs (\<Delta>, x <: T\<^sub>1)" by (metis pairs_dom pairs_extend)
  then show ?case by (meson SA_All Ty.SA_All well_scoped(1))
qed (auto simp: Ty.intros pairs_dom)

lemma closed_in_concat: "dom \<Gamma> \<inter> dom \<Delta> = {} \<Longrightarrow> T closed_in \<Gamma> \<Longrightarrow> T closed_in (\<Gamma>, \<Delta>)"
  by transfer auto
lemma in_context_concat: "dom \<Gamma> \<inter> dom \<Delta> = {} \<Longrightarrow> x <: T \<in> \<Gamma> \<Longrightarrow> x <: T \<in> \<Gamma>,\<Delta>"
  by transfer auto
lemma dom_concat[simp]: "dom \<Gamma> \<inter> dom \<Delta> = {} \<Longrightarrow> dom (\<Gamma>, \<Delta>) = dom \<Gamma> \<union> dom \<Delta>"
  by transfer auto
lemma pairs_concat[simp]: "dom \<Gamma> \<inter> dom \<Delta> = {} \<Longrightarrow> pairs (\<Gamma>, \<Delta>) = pairs \<Gamma> \<union> pairs \<Delta>"
  by transfer auto

lemma Ty_weakening: "\<lbrakk> \<Gamma> \<turnstile> S <: T ; dom \<Gamma> \<inter> dom \<Delta> = {} \<rbrakk> \<Longrightarrow> \<Gamma>,\<Delta> \<turnstile> S <: T"
proof (binder_induction \<Gamma> S T avoiding: "dom \<Delta>" rule: Ty_strong_induct)
  case (SA_Top \<Gamma> S)
  then show ?case  using Ty.SA_Top closed_in_concat by presburger
next
  case (SA_Refl_TVar \<Gamma> x)
  then show ?case using Ty.SA_Refl_TVar closed_in_concat by presburger
next
  case (SA_Trans_TVar x U \<Gamma> T)
  then show ?case using in_context_concat by blast
next
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2)
  have "pairs ((\<Gamma> , x <: T\<^sub>1), \<Delta>) = pairs ((\<Gamma>, \<Delta>), x <: T\<^sub>1)"
    using SA_All(1, 3, 6, 7, 8) well_scoped(1) by fastforce
  then have "(\<Gamma>, \<Delta>), x <: T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2" using Ty_permute SA_All by auto
  then show ?case  using SA_All Ty.SA_All well_scoped(1) by auto
qed (auto simp: Ty.intros)

lemma extend_assoc: "\<lbrakk> dom \<Gamma> \<inter> dom \<Delta> = {} ; X \<notin> dom \<Gamma> ; X \<notin> dom \<Delta> ; T closed_in \<Delta> \<rbrakk> \<Longrightarrow> \<Gamma>, \<Delta> , X <: T = \<Gamma>, (\<Delta> , X <: T)"
  by transfer (auto split: if_splits)

lemma Ty_well_formed :
  assumes "X \<notin> dom \<Gamma>" "(\<Gamma> , X <: Q) , \<Delta> \<turnstile> M <: N" "\<Gamma> \<turnstile> R <: Q"
  shows "M closed_in (\<Gamma> , X <: R) , \<Delta>" and "N closed_in (\<Gamma> , X <: R) , \<Delta>"
  using well_scoped dom_concat dom_extend assms
  by (smt (verit, best) concat.rep_eq dom.rep_eq)+

lemma Ty_transitivity : "\<lbrakk> \<Gamma> \<turnstile> S <: Q ; \<Gamma> \<turnstile> Q <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  and Ty_narrowing : "\<lbrakk> dom \<Gamma> \<inter> dom \<Delta> = {} ; X \<notin> dom \<Gamma> ; X \<notin> dom \<Delta> ; (\<Gamma> , X <: Q) , \<Delta> \<turnstile> M <: N ; \<Gamma> \<turnstile> R <: Q \<rbrakk> \<Longrightarrow> (\<Gamma> , X <: R) , \<Delta> \<turnstile> M <: N"
proof (binder_induction Q arbitrary: \<Gamma> \<Delta> avoiding: "dom \<Gamma>" "dom \<Delta>" rule: typ.strong_induct)
  case (TyVar Y \<Gamma> \<Delta>)
  show trans: "\<Gamma> \<turnstile> S <: TyVar Y \<Longrightarrow> \<Gamma> \<turnstile> TyVar Y <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
    by (induction \<Gamma> S "TyVar Y" rule: Ty.induct) auto
  {
    case Ty_narrowing: 2
    then have closed: "M closed_in (\<Gamma> , X <: R) , \<Delta>" "N closed_in (\<Gamma> , X <: R) , \<Delta>"
      using Ty_well_formed by simp_all
    have closed2: "TyVar Y closed_in \<Gamma>" using well_scoped Ty_narrowing by blast
    from Ty_narrowing(4,1-3,5) closed show ?case
    proof (induction "(\<Gamma> , X <: TyVar Y), \<Delta>" M N arbitrary: \<Delta>  rule: Ty.induct)
      case (SA_Trans_TVar Z U T)
      then show ?case sorry
    next
      case (SA_All T\<^sub>1 S\<^sub>1 Z S\<^sub>2 T\<^sub>2)
      have "(\<Gamma> , X <: TyVar Y), \<Delta> , Z <: T\<^sub>1 = (\<Gamma> , X <: TyVar Y), (\<Delta> , Z <: T\<^sub>1)"
        apply (rule extend_assoc)
        apply (metis (no_types, lifting) Int_Un_distrib2 Int_Un_eq(4) SA_All.prems(1) SA_All.prems(2) SA_All.prems(3) SA_All.prems(4) disjoint_single dom_extend inf_sup_aci(4) well_scoped(2))
        using SA_All.hyps(5) SA_All.prems(1) SA_All.prems(2) SA_All.prems(3) SA_All.prems(4) well_scoped(2) apply fastforce
        using SA_All.hyps(5) SA_All.prems(1) SA_All.prems(2) SA_All.prems(3) SA_All.prems(4) well_scoped(2) apply fastforce
        
        sorry
      have "(\<Gamma> , X <: R), (\<Delta>, Z <: T\<^sub>1) \<turnstile> S\<^sub>2 <: T\<^sub>2"
        apply (rule SA_All(4))

      show ?case
        apply (rule Ty.SA_All)
        using SA_All
           apply simp
        using SA_All
        sorry
    qed auto
  }
next
  case (Top \<Gamma> X \<Delta>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Fun x1 x2 \<Gamma> X \<Delta>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Forall x1 x2 x3 \<Gamma> X \<Delta>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
qed simp_all




end