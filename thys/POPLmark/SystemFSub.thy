(* System F with Subtyping  *)
theory SystemFSub
  imports "../MRBNF_Recursor"
    "../Instantiation_Infrastructure/Curry_LFP"
    "../Generic_Barendregt_Enhanced_Rule_Induction"
    "../Instantiation_Infrastructure/FixedCountableVars"
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

lemma typ_inject:
  "TyVar x = TyVar y \<longleftrightarrow> x = y"
  "Fun T1 T2 = Fun R1 R2 \<longleftrightarrow> T1 = R1 \<and> T2 = R2"
  "Forall x T1 T2 = Forall y R1 R2 \<longleftrightarrow> T1 = R1 \<and> (\<exists>f. bij (f::'a::var_typ_pre \<Rightarrow> 'a) \<and> |supp f| <o |UNIV::'a set| \<and> id_on (FFVars_typ T2 - {x}) f \<and> f x = y \<and> rrename_typ f T2 = R2)"
    apply (unfold TyVar_def Fun_def Forall_def typ.TT_injects0
      set3_typ_pre_def comp_def Abs_typ_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_typ_pre_def
      prod.map_id set2_typ_pre_def prod_set_simps prod.set_map UN_single Abs_typ_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp
    )
  by auto
declare typ_inject(1,2)[simp]

corollary Forall_inject_same[simp]: "Forall x T1 T2 = Forall x R1 R2 \<longleftrightarrow> T1 = R1 \<and> T2 = R2"
  using typ_inject(3) typ.rrename_cong_ids
  by (metis (no_types, lifting) Diff_empty Diff_insert0 id_on_insert insert_Diff)

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
abbreviation extend :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau>" ("_ , _ <: _" [57,75,75] 71) where
  "extend \<Gamma> x T \<equiv> (x, T)#\<Gamma>"
abbreviation concat :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>" (infixl "(,)" 71) where
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

declare [[inductive_internals]]

notation Fun (infixr "\<rightarrow>" 65)
notation Forall ("\<forall> _ <: _ . _" [62, 62, 62] 70)

abbreviation in_context :: "var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ <: _ \<in> _" [55,55,55] 60) where
  "x <: t \<in> \<Gamma> \<equiv> (x, t) \<in> set \<Gamma>"
abbreviation well_scoped :: "type \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ closed'_in _" [55, 55] 60) where
  "well_scoped S \<Gamma> \<equiv> FFVars_typ S \<subseteq> dom \<Gamma>"

inductive wf_ty :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("\<turnstile> _ ok" [70] 100) where
  wf_Nil[intro]: "\<turnstile> [] ok"
| wf_Cons[intro!]: "\<lbrakk> x \<notin> dom \<Gamma> ; T closed_in \<Gamma> ; \<turnstile> \<Gamma> ok \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>,x<:T ok"

inductive_cases
  wfE[elim]: "\<turnstile> \<Gamma> ok"
  and wf_ConsE[elim!]: "\<turnstile> (a#\<Gamma>) ok"
print_theorems

inductive ty :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [55,55,55] 60) where
  SA_Top: "\<lbrakk> \<turnstile> \<Gamma> ok ; S closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_Refl_TVar: "\<lbrakk> \<turnstile> \<Gamma> ok ; TyVar x closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: TyVar x"
| SA_Trans_TVar: "\<lbrakk> x<:U \<in> \<Gamma> ; \<Gamma> \<turnstile> U <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: T"
| SA_Arrow: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_All: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma>, x<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<forall>x<:S\<^sub>1. S\<^sub>2 <: \<forall>x<:T\<^sub>1 .T\<^sub>2"

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

lemma wf_context: "\<Gamma> \<turnstile> S <: T \<Longrightarrow> \<turnstile> \<Gamma> ok"
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

thm ty_def
declare ty.intros[intro]

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
  "Tfvars (\<Gamma>, T\<^sub>1, T\<^sub>2) = dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<union> FFVars_typ T\<^sub>1 \<union> FFVars_typ T\<^sub>2"

(* definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where
  "Vmap \<equiv> map"
fun Vfvars :: "V \<Rightarrow> var set" where
  "Vfvars v = set v"
*)

interpretation Components where dummy = "undefined :: var" and
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def 
  using small_Un small_def typ.card_of_FFVars_bounds
         apply (auto simp: typ.FFVars_rrenames map_prod.comp typ.rrename_comp0s inf_A)
    apply (rule var_typ_pre_class.Un_bound var_typ_pre_class.UN_bound context_set_bd_UNIV set_bd_UNIV
        typ.card_of_FFVars_bounds)+
      apply (auto simp: context_map_cong_id typ.rrename_cong_ids intro: context_map_cong_id)
    apply (smt (verit, del_insts) UnI1 fst_conv imageI)
  apply (unfold map_context_def)[1]
   apply (smt (verit, del_insts) UN_I UnI1 UnI2 image_iff list.set_map prod_fun_imageE snd_conv typ.FFVars_rrenames)
  done

(* AtoJ: I have now removed the extra hypotheses for G, since 
we are using the "enhanced" version *)
definition G :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool" where
  "G \<equiv> \<lambda>B R t.
    (B = {} \<and> snd (snd t) = Top \<and> \<turnstile> fst t ok \<and> fst (snd t) closed_in fst t)
  \<or> (\<exists>x. B = {} \<and> fst (snd t) = TyVar x \<and> fst (snd t) = snd (snd t) \<and> \<turnstile> fst t ok \<and> fst (snd t) closed_in fst t)
  \<or> (\<exists>x U \<Gamma> T. B = {} \<and> fst t = \<Gamma> \<and> fst (snd t) = TyVar x \<and> snd (snd t) = T \<and> x <: U \<in> \<Gamma> \<and> R (\<Gamma>, U, T) 
   \<comment> \<open>\<and> \<Gamma> \<turnstile> U <: T\<close>)
  \<or> (\<exists>\<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2. B = {} \<and> fst t = \<Gamma> \<and> fst (snd t) = (S\<^sub>1 \<rightarrow> S\<^sub>2) \<and> snd (snd t) = (T\<^sub>1 \<rightarrow> T\<^sub>2) \<and> 
     R (\<Gamma>, T\<^sub>1, S\<^sub>1) \<comment> \<open> \<and> \<Gamma> \<turnstile> T1 <: S1 \<close> \<and> 
     R (\<Gamma>, S\<^sub>2, T\<^sub>2) \<comment> \<open> \<and> \<Gamma> \<turnstile> S2 <: T2 \<close> )
  \<or> (\<exists>\<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2. B = {x} \<and> fst t = \<Gamma> \<and> fst (snd t) = (\<forall>x<:S\<^sub>1. S\<^sub>2) \<and> snd (snd t) = (\<forall>x<:T\<^sub>1. T\<^sub>2) \<and> 
     R (\<Gamma>, T\<^sub>1, S\<^sub>1) \<comment> \<open>\<and> \<Gamma> \<turnstile> T1 <: S1 \<close> \<and> 
     R (\<Gamma>,x<:T\<^sub>1, S\<^sub>2, T\<^sub>2) \<comment> \<open>\<and> \<Gamma>,x<:T1 \<turnstile> S2 <: T2 \<close>)
  "

lemma G_mono: "R \<le> R' \<Longrightarrow> G v R t \<Longrightarrow> G v R' t"
  unfolding G_def by fastforce

lemma in_context_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "x <: T \<in> \<Gamma> \<Longrightarrow> f x <: rrename_typ f T \<in> map_context f \<Gamma>"
  using assms unfolding map_context_def by auto

lemma extend_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "map_context f (\<Gamma>,x<:T) = map_context f \<Gamma>,f x <: rrename_typ f T"
  using assms unfolding map_context_def by simp

lemma closed_in_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "S closed_in \<Gamma> \<Longrightarrow> rrename_typ f S closed_in map_context f \<Gamma>"
  using assms by (auto simp: typ.FFVars_rrenames)

lemma wf_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "\<turnstile> \<Gamma> ok \<Longrightarrow> \<turnstile> map_context f \<Gamma> ok"
unfolding map_context_def proof (induction \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case using assms apply auto  
    apply (metis fst_conv image_iff)
    using closed_in_eqvt map_context_def by fastforce
qed simp

lemma ty_eqvt:
  assumes "\<Gamma> \<turnstile> S <: T" "bij f" "|supp f| <o |UNIV::var set|"
  shows "map_context f \<Gamma> \<turnstile> rrename_typ f S <: rrename_typ f T"
  using assms proof (induction \<Gamma> S T rule: ty.induct)
  case (SA_Top \<Gamma> S)
  then show ?case by (auto intro!: ty.SA_Top dest: wf_eqvt closed_in_eqvt)
next
  case (SA_Refl_TVar \<Gamma> x)
  then show ?case
    apply (auto intro!: ty.SA_Refl_TVar imageI dest: wf_eqvt closed_in_eqvt)
    by (metis fst_conv image_iff)
next
  case (SA_Trans_TVar x U \<Gamma> T)
  then show ?case by (auto intro!: ty.SA_Trans_TVar dest: in_context_eqvt)
next
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2)
  then show ?case by (auto intro!: ty.SA_All simp: extend_eqvt)
qed auto

lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G (image \<sigma> B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
  unfolding G_def
  by (elim disj_forward exE; cases t)
    (auto simp: Tmap_def ssbij_def supp_inv_bound
      typ.rrename_comps typ.FFVars_rrenames wf_eqvt extend_eqvt
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "rrename_typ \<sigma> _"])+, (rule conjI)?, rule in_context_eqvt))+
(*
  unfolding G_def
  apply (elim disjE)
  subgoal
    apply (rule disjI1)
    apply (cases t)
    unfolding ssbij_def Tmap_def using closed_in_eqvt wf_eqvt by simp
  subgoal
    apply (rule disjI2, rule disjI1)
    apply (erule exE)
    apply (elim conjE)
    subgoal for x
      apply (cases t)
      unfolding ssbij_def Tmap_def using wf_eqvt by auto
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
      unfolding ssbij_def Tmap_def 
      apply (auto simp: in_context_eqvt supp_inv_bound typ.rrename_comps typ.rrename_comp0s ty_eqvt)
      done
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
      apply (cases t) unfolding ssbij_def Tmap_def 
      by (auto simp: in_context_eqvt supp_inv_bound
          typ.rrename_comps typ.rrename_comp0s ty_eqvt)
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
    apply (cases t) unfolding ssbij_def Tmap_def
    apply (auto simp: in_context_eqvt supp_inv_bound typ.FFVars_rrenames
          typ.rrename_comps typ.rrename_comp0s extend_eqvt[symmetric] wf_eqvt ty_eqvt
      )
    done
  done
*)

lemma fresh: "\<exists>xx. xx \<notin> Tfvars t"
  by (metis emp_bound equals0D imageI inf.commute inf_absorb2 small_Tfvars small_def small_ssbij subsetI)

lemma swap_idemp[simp]: "id(x := x) = id" by auto
lemma swap_left: "(id(x := xx, xx := x)) x = xx" by simp

lemma wf_FFVars: "\<turnstile> \<Gamma> ok \<Longrightarrow> a \<in> FFVars_ctxt \<Gamma> \<Longrightarrow> a \<in> dom \<Gamma>"
  by (induction \<Gamma>) auto

lemma finite_Tfvars: "finite (Tfvars t)"
using finite_iff_le_card_var small_Tfvars small_def by blast

lemma ls_UNIV_iff_finite: "|A| <o |UNIV::var set| \<longleftrightarrow> finite A"
using finite_iff_le_card_var by blast

lemma exists_fresh:
"\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set ts. z \<notin> Tfvars t)"
proof-
  have 0: "|set xs \<union> \<Union> (Tfvars ` (set ts))| <o |UNIV::var set|" 
  unfolding ls_UNIV_iff_finite  
  using finite_Tfvars by blast
  then obtain x where "x \<notin> set xs \<union> \<Union> (Tfvars ` (set ts))"
  by (meson exists_fresh) 
  thus ?thesis by auto
qed

abbreviation Ii where "Ii \<equiv> \<lambda>(\<Gamma>,S,T). \<Gamma> \<turnstile> S <: T"

lemma rrename_swap_FFvars[simp]: "x \<notin> FFVars_typ T \<Longrightarrow> xx \<notin> FFVars_typ T \<Longrightarrow> 
  rrename_typ (id(x := xx, xx := x)) T = T"
apply(rule typ.rrename_cong_ids) by auto

lemma map_context_swap_FFVars[simp]: 
"\<forall>k\<in>set \<Gamma>. x \<noteq> fst k \<and> x \<notin> FFVars_typ (snd k) \<and> 
           xx \<noteq> fst k \<and> xx \<notin> FFVars_typ (snd k) \<Longrightarrow> 
    map_context (id(x := xx, xx := x)) \<Gamma> = \<Gamma>"
  unfolding map_context_def apply(rule map_idI) by auto

lemma ssbij_swap: "ssbij (id(x := z, z := x))"
  unfolding ssbij_def by auto

lemma G_refresh:
  assumes "(\<And>t. R t \<Longrightarrow> Ii t)" "(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t))"
  shows "small B \<Longrightarrow> G B R t \<Longrightarrow>
  \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G C R t"
  unfolding G_def Tmap_def
    (**)ssbij_def conj_assoc[symmetric]
  unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
  apply (elim disj_forward exE; clarsimp)
   apply (((rule exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI[rotated]], assumption) |
        (((rule exI)+)?, (rule conjI)?, rule Forall_rrename) |
        (cases t; auto))+) []
  subgoal for T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2
    using exists_fresh[of "[x]" "[t]"] apply(elim exE conjE)
    subgoal for z
      apply (rule exI)
      apply (rule exI[of _ "{z}"])
      apply (intro exI conjI)
             apply (rule refl)+
           apply (rule Forall_swap)
           apply (cases t; simp)
          apply (rule Forall_swap)
          apply (cases t; simp)
         apply assumption+
        apply (frule assms(1)[of "((fst t, x <: T\<^sub>1), S\<^sub>2, T\<^sub>2)"])
        apply (drule assms(2)[rule_format, OF conjI, OF ssbij_swap, of "((fst t, x <: T\<^sub>1), S\<^sub>2, T\<^sub>2)" x z])
        apply (auto simp: Tmap_def extend_eqvt)
      apply (subst (asm) rrename_swap_FFvars)
        apply (cases t; simp)
        apply (metis fst_conv insert_Diff insert_subset snd_conv wf_ConsE wf_context)
       apply (cases t; simp)
      apply (subst (asm) map_context_swap_FFVars)
       apply (cases t; simp)
       apply (metis Pair_inject UN_I rev_image_eqI wf_ConsE wf_FFVars wf_context)
      apply assumption
      done
    done
  done
(*
unfolding G_def Tmap_def apply safe
  subgoal by (rule exI[of _ "{}"]) auto
  subgoal by (rule exI[of _ "{}"]) auto
  subgoal by (rule exI[of _ "{}"]) auto
  subgoal by (rule exI[of _ "{}"]) fastforce
  subgoal for \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2
  using exists_fresh[of "[x]" "[t]"] apply(elim exE conjE)
  subgoal for xx apply (rule exI[of _ "{xx}"])
  apply (intro conjI)
    subgoal by simp 
    subgoal by simp 
    subgoal apply(rule disjI5_5)
    apply(rule exI[of _ "fst t"])  
    apply (rule exI[of _ "T\<^sub>1"])
    apply (rule exI[of _ "S\<^sub>1"])
    apply (rule exI[of _ "xx"])
    apply (rule exI[of _ "rrename_typ (id(x:=xx,xx:=x)) S\<^sub>2"])
    apply (rule exI[of _ "rrename_typ (id(x:=xx,xx:=x)) T\<^sub>2"])
    apply (cases t) apply simp apply (intro conjI)
      subgoal apply (subst Forall_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply (subst Forall_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal for \<Gamma> _ _ apply(erule allE[of _ "id(x:=xx,xx:=x)"])
      apply(erule allE[of _ "\<Gamma> , x <: T\<^sub>1"])
      apply(erule allE[of _ S\<^sub>2]) apply(erule allE[of _ T\<^sub>2])
      subgoal premises P using P(2-)
      using wf_FFVars[OF wf_context[OF P(1)[OF P(5)]]]
      wf_context[OF P(1)[OF P(6)]]
      apply(subgoal_tac "(\<forall>k\<in>set \<Gamma>. x \<noteq> fst k \<and> x \<notin> FFVars_typ (snd k)) \<and> 
                         x \<notin> FFVars_typ T\<^sub>1")
      apply(subst (asm) extend_eqvt, simp, simp)
      subgoal apply (auto simp add: ssbij_def) 
      by (metis image_eqI map_context_swap_FFVars) 
      subgoal by (auto simp add: ssbij_def) . . . . . .
*)

(* AtoJ: I also ported the original proof (below), but I think the above 
one is more maintainable. 
  using fresh[of t] unfolding G_def Tmap_def apply safe
  subgoal by (rule exI[of _ "{}"]) auto
  subgoal by (rule exI[of _ "{}"]) auto
  subgoal by (rule exI[of _ "{}"]) auto
  subgoal by (rule exI[of _ "{}"]) fastforce
  subgoal for xx \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2
    apply (rule exI[of _ "{xx}"])
    apply (rule conjI)
    subgoal by auto
    apply(rule conjI, simp) 
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
    subgoal for a b c subgoal premises P
    using P(2-) apply -
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
     apply auto[1]
    apply (subst extend_eqvt)
      apply (rule bij_swap)
     apply (rule supp_swap_bound)
      apply (rule infinite_var)
    apply (rule arg_cong3[of _ _ _ _ _ _ extend])
      apply (rule sym)
      apply (rule context_map_cong_id)
        apply (rule bij_swap)
       apply (rule supp_swap_bound)
       apply (rule infinite_var)
       apply (erule UnE)
        apply auto[1]  
        apply (metis P(1) fst_conv image_eqI wf_ConsE wf_context)
       apply (drule wf_FFVars[rotated])  
        apply (meson P(1) wf_context) 
       apply (metis P(1) fst_conv fun_upd_apply id_apply wf_ConsE wf_context)
     apply simp
     apply (smt (verit) P(1) Prelim.bij_swap fst_conv fun_upd_apply 
       id_apply infinite_var list.discI list.inject subset_eq 
       supp_swap_bound typ.rrename_cong_ids well_scoped(1) 
       wf_ty.cases wf_context) . . . .
*)

(* The name "PM" of this interpretation stands for "POPLmark" *)
interpretation Ty: Induct1 where dummy = "undefined :: var"
  and Tmap = Tmap and Tfvars = Tfvars and G = G
  apply standard
  using G_mono G_equiv  by auto 

(* AtoJ: Now the proof of this is completely standard, 
bacause we use the original operator G:  *)
lemma ty_I: "ty \<Gamma> T1 T2 = Ty.I (\<Gamma>, T1, T2)"
unfolding ty_def Ty.I_def lfp_curry3 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R \<Gamma>\<Gamma> TT1 TT2 apply(rule iffI)
  subgoal apply(elim disjE exE)
    \<^cancel>\<open>SA_Top: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI5_1) by auto
    \<^cancel>\<open>SA_Refl_TVar: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI5_2) by auto
    \<^cancel>\<open>SA_Trans_TVar: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI5_3) by auto
    \<^cancel>\<open>SA_Arrow: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI5_4) by auto 
    \<^cancel>\<open>SA_All: \<close>
    subgoal for T\<^sub>1 S\<^sub>1 x S\<^sub>2 
    apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI5_5) by auto .
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>SA_Top: \<close>
    subgoal apply(rule disjI5_1) by auto
    \<^cancel>\<open>SA_Refl_TVar: \<close>
    subgoal apply(rule disjI5_2) by auto
    \<^cancel>\<open>SA_Trans_TVar: \<close>
    subgoal apply(rule disjI5_3) by auto
    \<^cancel>\<open>SA_Arrow: \<close>
    subgoal apply(rule disjI5_4) by auto 
    \<^cancel>\<open>SA_All: \<close>
    subgoal for v \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2
    apply(rule disjI5_5) by fastforce . . .

interpretation ty: Induct where dummy = "undefined :: var"
  and Tmap = Tmap and Tfvars = Tfvars and G = G
  apply standard subgoal for R B t
  using G_refresh[of R B t] unfolding ty_I by auto .
print_theorems

corollary strong_induct_ty[consumes 2, case_names ty SA_Top SA_Refl_TVar SA_Trans_TVar SA_Arrow SA_All]: 
assumes par: "\<And>p. small (Pfvars p)" 
and ty: "\<Gamma> \<turnstile> S <: T" 
and SA_Top: "\<And>\<Gamma> S p. 
   \<turnstile> \<Gamma> ok \<Longrightarrow> S closed_in \<Gamma> \<Longrightarrow> 
   \<phi> p \<Gamma> S Top"
and SA_Refl_TVar: "\<And>\<Gamma> x p. 
   \<turnstile> \<Gamma> ok \<Longrightarrow> TyVar x closed_in \<Gamma> \<Longrightarrow> 
   \<phi> p \<Gamma> (TyVar x) (TyVar x)"
and SA_Trans_TVar: "\<And>x U \<Gamma> T p. 
   x <: U \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> U <: T \<Longrightarrow> \<forall>p. \<phi> p \<Gamma> U T \<Longrightarrow> 
   \<phi> p \<Gamma> (TyVar x) T"
and SA_Arrow: "\<And>\<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 p. 
   \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<forall>p. \<phi> p \<Gamma> T\<^sub>1 S\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> \<forall>p. \<phi> p \<Gamma> S\<^sub>2 T\<^sub>2 \<Longrightarrow> 
   \<phi> p \<Gamma> (S\<^sub>1 \<rightarrow> S\<^sub>2) (T\<^sub>1 \<rightarrow> T\<^sub>2)" 
and SA_All: "\<And>\<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 p. 
   x \<notin> Pfvars p \<Longrightarrow> x \<notin> dom \<Gamma> \<Longrightarrow> x \<notin> FFVars_typ S\<^sub>1 \<Longrightarrow> x \<notin> FFVars_typ T\<^sub>1 \<Longrightarrow> 
   \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<forall>p. \<phi> p \<Gamma> T\<^sub>1 S\<^sub>1 \<Longrightarrow> \<Gamma> , x <: T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> 
   \<forall>p. \<phi> p (\<Gamma> , x <: T\<^sub>1) S\<^sub>2 T\<^sub>2 \<Longrightarrow> 
   \<phi> p \<Gamma> (\<forall> x <: S\<^sub>1 . S\<^sub>2) (\<forall> x <: T\<^sub>1 . T\<^sub>2)"
shows "\<phi> p \<Gamma> S T"
apply(subgoal_tac "case (\<Gamma>, S, T) of (\<Gamma>, S, T) \<Rightarrow> \<phi> p \<Gamma> S T")
  subgoal by simp
  subgoal using par ty
  apply(elim ty.strong_induct[where R = "\<lambda>p (\<Gamma>, S, T). \<phi> p \<Gamma> S T"])
    subgoal using ty_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding ty_I[symmetric] apply(elim disjE exE)
      subgoal using SA_Top by auto
      subgoal for X using SA_Refl_TVar[of _ X p] by auto
      subgoal using SA_Trans_TVar by auto
      subgoal using SA_Arrow by auto
      subgoal using SA_All by auto . . .

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_step:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "\<Gamma> \<turnstile> U <: T" 
shows "(map_context f \<Gamma>) \<turnstile> (rrename_typ f U) <: (rrename_typ f T)"
using assms unfolding ty_I using Ty.I_equiv[of "(\<Gamma>,U,T)" f]
unfolding Tmap_def ssbij_def by auto


end
