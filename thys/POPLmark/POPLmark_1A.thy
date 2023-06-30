theory POPLmark_1A
  imports "../MRBNF_Recursor"
    "../../DAList" "../Instantiation_Infrastructure/FixedCountableVars"
    "../Instantiation_Infrastructure/Curry_LFP"
    "../Generic_Barendregt_Enhanced_Rule_Induction"
begin

declare bij_swap[simp]

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
type_synonym \<Gamma>\<^sub>\<tau> = "(var, type) dalist"

declare [[inductive_internals]]

notation Fun (infixr "\<rightarrow>" 65)
notation Forall ("\<forall> _ <: _ . _" [62, 62, 62] 70)

abbreviation in_context :: "var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ <: _ \<in> _" [55,55,55] 60) where
  "x <: t \<in> \<Gamma> \<equiv> (x, t) \<in> pairs_dalist \<Gamma>"
abbreviation extend :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau>" ("_ , _ <: _" [57,57,57] 62) where
  "\<Gamma>, x<:t \<equiv> insert_dalist x t \<Gamma>"
abbreviation map_context :: "(var \<Rightarrow> var) \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>" where
  "map_context f \<equiv> map_dalist f (rrename_typ f)"
abbreviation dom :: "('k, 'v) dalist \<Rightarrow> 'k set" where "dom \<equiv> keys_dalist"
abbreviation empty :: "'a set" ("\<emptyset>") where "empty \<equiv> {}"
abbreviation concat :: "('k, 'v) dalist \<Rightarrow> ('k, 'v) dalist \<Rightarrow> ('k, 'v) dalist" ("_, _" [65,65] 70) where
  "concat \<equiv> concat_dalist"

inductive Ty :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [55,55,55] 60) where
  SA_Top:         "\<Gamma> \<turnstile> S <: Top"
| SA_Refl_TVar:   "\<Gamma> \<turnstile> TyVar x <: TyVar x"
| SA_Trans_TVar:  "\<lbrakk> x<:U \<in> \<Gamma> ; \<Gamma> \<turnstile> U <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: T"
| SA_Arrow:       "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_All:         "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma>, x<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<forall>x<:S\<^sub>1. S\<^sub>2 <: \<forall>x<:T\<^sub>1 .T\<^sub>2" (* potentially needs "x \<notin> dom \<Gamma>" as assumption *)

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
  "Tfvars (\<Gamma>, T\<^sub>1, T\<^sub>2) = keys_dalist \<Gamma> \<union> \<Union>(FFVars_typ ` vals_dalist \<Gamma>) \<union> FFVars_typ T\<^sub>1 \<union> FFVars_typ T\<^sub>2"

definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where
  "Vmap \<equiv> map"
fun Vfvars :: "V \<Rightarrow> var set" where
  "Vfvars v = set v"

interpretation Components where dummy = "undefined :: var" and
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars
apply standard unfolding ssbij_def Tmap_def Vmap_def
  using small_Un small_def typ.card_of_FFVars_bounds
         apply (auto simp: typ.FFVars_rrenames dalist.map_id0 map_prod.comp dalist.set_map dalist.map_comp typ.rrename_comp0s inf_A)
    apply (rule var_typ_pre_class.Un_bound var_typ_pre_class.UN_bound
        typ.card_of_FFVars_bounds dalist.set_bd[THEN ordLess_ordLeq_trans[OF _ var_typ_pre_class.large]])+
     apply auto
    apply (rule sym)
    apply (rule trans[OF dalist.map_id[symmetric]])
    apply (rule dalist.map_cong)
          apply (rule bij_id supp_id_bound refl | assumption)+
     apply (rule trans[OF id_apply])
     apply (rule sym)
     apply (erule ballE)
      apply assumption
     apply (erule notE)
     apply (rule UnI1)+
     apply assumption
    apply (rule trans[OF id_apply])
    apply (rule sym)
    apply (rule typ.rrename_cong_ids)
      apply assumption+
    apply (erule ballE)
     apply assumption
    apply (erule notE)
    apply (rule UnI1, rule UnI1, rule UnI2)
    apply (rule UN_I)
     apply assumption+
   apply (rule typ.rrename_cong_ids)
      apply assumption+
    apply (erule ballE)
     apply assumption
    apply (erule notE)
    apply (rule UnI1, rule UnI2)
     apply assumption
   apply (rule typ.rrename_cong_ids)
      apply assumption+
    apply (erule ballE)
     apply assumption
    apply (erule notE)
    apply (rule UnI2)
  apply assumption
  done

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> T \<Rightarrow> bool" where
  "G \<equiv> \<lambda>R v t.
    (v = [] \<and> snd (snd t) = Top)
  \<or> (\<exists>x. v = [] \<and> fst (snd t) = TyVar x \<and> fst (snd t) = snd (snd t))
  \<or> (\<exists>x U \<Gamma> T. v = [] \<and> fst t = \<Gamma> \<and> fst (snd t) = TyVar x \<and> snd (snd t) = T \<and> x <: U \<in> \<Gamma> \<and> R (\<Gamma>, U, T))
  \<or> (\<exists>\<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2. v = [] \<and> fst t = \<Gamma> \<and> fst (snd t) = (S\<^sub>1 \<rightarrow> S\<^sub>2) \<and> snd (snd t) = (T\<^sub>1 \<rightarrow> T\<^sub>2) \<and> R (\<Gamma>, T\<^sub>1, S\<^sub>1) \<and> R (\<Gamma>, S\<^sub>2, T\<^sub>2))
  \<or> (\<exists>\<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2. v = [x] \<and> fst t = \<Gamma> \<and> fst (snd t) = (\<forall>x<:S\<^sub>1. S\<^sub>2) \<and> snd (snd t) = (\<forall>x<:T\<^sub>1. T\<^sub>2) \<and> R (\<Gamma>, T\<^sub>1, S\<^sub>1) \<and> R (\<Gamma>,x<:T\<^sub>1, S\<^sub>2, T\<^sub>2))
  "

lemma GG_mono: "R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
  unfolding G_def by fastforce

lemma in_context_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "x <: T \<in> \<Gamma> \<Longrightarrow> f x <: rrename_typ f T \<in> map_dalist f (rrename_typ f) \<Gamma>"
  using assms by transfer (auto simp: inj_on_def)

lemma extend_eqvt:
  assumes "bij f" "|supp f| <o |UNIV::var set|"
  shows "map_context f (\<Gamma>,x<:T) = map_context f \<Gamma>,f x <: rrename_typ f T"
  using assms by transfer (auto simp: inj_on_def image_iff)

lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
  unfolding G_def
  apply (elim disjE)
  subgoal
    apply (rule disjI1)
    apply (cases t)
    unfolding ssbij_def Tmap_def Vmap_def by simp
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
      apply (rule exI[of _ "map_dalist \<sigma> (rrename_typ \<sigma>) \<Gamma>"])
      apply (rule exI[of _ "rrename_typ \<sigma> T"])
      apply (cases t)
      unfolding ssbij_def Tmap_def Vmap_def
      by (auto simp: in_context_eqvt dalist.map_comp supp_inv_bound
          typ.rrename_comps typ.rrename_comp0s dalist.map_id)
    done
  subgoal
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
    apply (elim exE conjE)
    subgoal for \<Gamma> T1 S1 S2 T2
      apply (rule exI[of _ "map_dalist \<sigma> (rrename_typ \<sigma>) \<Gamma>"])
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
          apply (rule exI[of _ "map_dalist \<sigma> (rrename_typ \<sigma>) \<Gamma>"])
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
    Union_empty image_insert image_empty map_typ_pre_def id_def
  )
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
    sorry
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
  by blast

corollary Ty_strong_induct[consumes 1, case_names Bound SA_Top SA_Refl_TVar SA_Trans_TVar SA_Arrow SA_All]:
  "\<Gamma> \<turnstile> S <: T \<Longrightarrow>
  \<forall>\<rho>. |K \<rho>| <o |UNIV::var set| \<Longrightarrow>
  (\<And>\<Gamma> S \<rho>. P \<Gamma> S Top \<rho>) \<Longrightarrow>
  (\<And>\<Gamma> x \<rho>. P \<Gamma> (TyVar x) (TyVar x) \<rho>) \<Longrightarrow>
  (\<And>x U \<Gamma> T \<rho>. x <: U \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> U <: T \<Longrightarrow> \<forall>\<rho>. P \<Gamma> U T \<rho> \<Longrightarrow> P \<Gamma> (TyVar x) T \<rho>) \<Longrightarrow>
  (\<And>\<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 \<rho>. \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> T\<^sub>1 S\<^sub>1 \<rho> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> S\<^sub>2 T\<^sub>2 \<rho> \<Longrightarrow> P \<Gamma> (S\<^sub>1 \<rightarrow> S\<^sub>2) (T\<^sub>1 \<rightarrow> T\<^sub>2) \<rho>) \<Longrightarrow>
  (\<And>\<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 \<rho>. x \<notin> K \<rho> \<Longrightarrow> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> T\<^sub>1 S\<^sub>1 \<rho> \<Longrightarrow> \<Gamma> , x <: T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> \<forall>\<rho>. P (\<Gamma> , x <: T\<^sub>1) S\<^sub>2 T\<^sub>2 \<rho> \<Longrightarrow> P \<Gamma> (\<forall> x <: S\<^sub>1 . S\<^sub>2) (\<forall> x <: T\<^sub>1 . T\<^sub>2) \<rho>) \<Longrightarrow>
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
lemma Ty_refl: "\<Gamma> \<turnstile> T <: T"
  by (induction arbitrary: \<Gamma>) auto

lemma Ty_permute: "\<lbrakk> \<Gamma> \<turnstile> S <: T ; pairs_dalist \<Gamma> = pairs_dalist \<Delta> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> S <: T"
proof (induction \<Gamma> S T arbitrary: \<Delta> rule: Ty.induct)
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2)
  then have "keys_dalist \<Gamma> = keys_dalist \<Delta>" by (metis fst_pairs_dalist)
  then have "pairs_dalist (\<Gamma>, x <: T\<^sub>1) = pairs_dalist (\<Delta>, x <: T\<^sub>1)"
    by (metis SA_All.prems pairs_insert_fresh pairs_insert_same)
  then show ?case using SA_All by blast
qed auto

lemma in_concat_dalist[simp]: "keys_dalist xs \<inter> keys_dalist ys = {} \<Longrightarrow> pairs_dalist (concat_dalist xs ys) = pairs_dalist xs \<union> pairs_dalist ys"
  by transfer auto

lemma Ty_weakening: "\<lbrakk> \<Gamma> \<turnstile> S <: T ; dom \<Gamma> \<inter> dom \<Delta> = \<emptyset> \<rbrakk> \<Longrightarrow> \<Gamma>,\<Delta> \<turnstile> S <: T"
proof (binder_induction \<Gamma> S T avoiding: \<Delta> rule: Ty_strong_induct)
(*proof (induction \<Gamma> S T arbitrary: \<Delta> rule: Ty.induct)
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2)
  then show ?case sorry
qed auto*)
  oops

end