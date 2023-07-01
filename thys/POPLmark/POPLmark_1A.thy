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
type_synonym \<Gamma>\<^sub>\<tau> = "(var \<times> type) list"

definition map_context :: "(var \<Rightarrow> var) \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>" where
  "map_context f \<equiv> map (map_prod f (rrename_typ f))"

abbreviation extend :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var \<Rightarrow> type \<Rightarrow> \<Gamma>\<^sub>\<tau>" ("_ , _ <: _" [57,75,75] 71) where
  "extend \<Gamma> x T \<equiv> (x, T)#\<Gamma>"
abbreviation concat :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau>" (infixl "(,)" 71) where
  "concat \<Gamma> \<Delta> \<equiv> \<Delta> @ \<Gamma>"
abbreviation empty_context :: "\<Gamma>\<^sub>\<tau>" ("\<emptyset>") where "empty_context \<equiv> []"
abbreviation dom :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> var set" where "dom xs \<equiv> fst ` set xs"

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
  and "\<And>a. a \<in> dom \<Gamma> \<union> \<Union>(FFVars_typ ` snd ` set \<Gamma>) \<Longrightarrow> f a = a"
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

inductive wf_Ty :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("\<turnstile> _ ok" [70] 100) where
  wf_Nil[intro]: "\<turnstile> [] ok"
| wf_Cons[intro!]: "\<lbrakk> x \<notin> dom \<Gamma> ; T closed_in \<Gamma> ; \<turnstile> \<Gamma> ok \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>,x<:T ok"

inductive_cases
  wfE[elim]: "\<turnstile> \<Gamma> ok"
  and wf_ConsE[elim!]: "\<turnstile> (a#\<Gamma>) ok"
print_theorems

inductive Ty :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [55,55,55] 60) where
  SA_Top: "\<lbrakk> \<turnstile> \<Gamma> ok ; S closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_Refl_TVar: "\<lbrakk> \<turnstile> \<Gamma> ok ; TyVar x closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: TyVar x"
| SA_Trans_TVar: "\<lbrakk> x<:U \<in> \<Gamma> ; \<Gamma> \<turnstile> U <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: T"
| SA_Arrow: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_All: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma>, x<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<forall>x<:S\<^sub>1. S\<^sub>2 <: \<forall>x<:T\<^sub>1 .T\<^sub>2"

lemma wf_context: "\<Gamma> \<turnstile> S <: T \<Longrightarrow> \<turnstile> \<Gamma> ok"
  by (induction \<Gamma> S T rule: Ty.induct)

lemma well_scoped:
  assumes "\<Gamma> \<turnstile> S <: T"
  shows "S closed_in \<Gamma>" "T closed_in \<Gamma>"
using assms proof (induction \<Gamma> S T rule: Ty.induct)
case (SA_Trans_TVar x U \<Gamma> T) {
  case 1 then show ?case using SA_Trans_TVar
    by (metis fst_conv imageI singletonD subsetI typ.set(1))
next
  case 2 then show ?case by (simp add: SA_Trans_TVar)
} qed auto

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
  "Tfvars (\<Gamma>, T\<^sub>1, T\<^sub>2) = dom \<Gamma> \<union> \<Union>(FFVars_typ ` snd ` set \<Gamma>) \<union> FFVars_typ T\<^sub>1 \<union> FFVars_typ T\<^sub>2"

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
    apply (rule var_typ_pre_class.Un_bound var_typ_pre_class.UN_bound context_set_bd_UNIV set_bd_UNIV
        typ.card_of_FFVars_bounds)+
      apply (auto simp: context_map_cong_id typ.rrename_cong_ids intro: context_map_cong_id)
    apply (smt (verit, del_insts) UnI1 fst_conv imageI)
  apply (unfold map_context_def)[1]
   apply (smt (verit, del_insts) UN_I UnI1 UnI2 image_iff list.set_map prod_fun_imageE snd_conv typ.FFVars_rrenames)
  done


definition G :: "(T \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> T \<Rightarrow> bool" where
  "G \<equiv> \<lambda>R v t.
    (v = [] \<and> snd (snd t) = Top \<and> \<turnstile> fst t ok \<and> fst (snd t) closed_in fst t)
  \<or> (\<exists>x. v = [] \<and> fst (snd t) = TyVar x \<and> fst (snd t) = snd (snd t) \<and> \<turnstile> fst t ok \<and> fst (snd t) closed_in fst t)
  \<or> (\<exists>x U \<Gamma> T. v = [] \<and> fst t = \<Gamma> \<and> fst (snd t) = TyVar x \<and> snd (snd t) = T \<and> x <: U \<in> \<Gamma> \<and> R (\<Gamma>, U, T) \<and> \<Gamma> \<turnstile> U <: T)
  \<or> (\<exists>\<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2. v = [] \<and> fst t = \<Gamma> \<and> fst (snd t) = (S\<^sub>1 \<rightarrow> S\<^sub>2) \<and> snd (snd t) = (T\<^sub>1 \<rightarrow> T\<^sub>2) \<and> R (\<Gamma>, T\<^sub>1, S\<^sub>1) \<and> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<and> R (\<Gamma>, S\<^sub>2, T\<^sub>2) \<and> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2)
  \<or> (\<exists>\<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2. v = [x] \<and> fst t = \<Gamma> \<and> fst (snd t) = (\<forall>x<:S\<^sub>1. S\<^sub>2) \<and> snd (snd t) = (\<forall>x<:T\<^sub>1. T\<^sub>2) \<and> R (\<Gamma>, T\<^sub>1, S\<^sub>1) \<and> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<and> R (\<Gamma>,x<:T\<^sub>1, S\<^sub>2, T\<^sub>2) \<and> \<Gamma>,x<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2)
  "

lemma GG_mono: "R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
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
  then show ?case using assms
    by (smt (verit) Product_Type.fst_comp_map_prod image_comp image_mono list.discI list.inject list.set_map list.simps(9) map_prod_simp not_imageI typ.FFVars_rrenames wf_Cons wf_Ty.cases)
qed simp

lemma Ty_eqvt:
  assumes "\<Gamma> \<turnstile> S <: T" "bij f" "|supp f| <o |UNIV::var set|"
  shows "map_context f \<Gamma> \<turnstile> rrename_typ f S <: rrename_typ f T"
  using assms proof (induction \<Gamma> S T rule: Ty.induct)
  case (SA_Top \<Gamma> S)
  then show ?case by (auto intro!: Ty.SA_Top dest: wf_eqvt closed_in_eqvt)
next
  case (SA_Refl_TVar \<Gamma> x)
  then show ?case
    apply (auto intro!: Ty.SA_Refl_TVar imageI dest: wf_eqvt closed_in_eqvt)
    by (metis fst_conv image_iff)
next
  case (SA_Trans_TVar x U \<Gamma> T)
  then show ?case by (auto intro!: Ty.SA_Trans_TVar dest: in_context_eqvt)
next
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2)
  then show ?case by (auto intro!: Ty.SA_All simp: extend_eqvt)
qed auto

lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
  unfolding G_def
  apply (elim disjE)
  subgoal
    apply (rule disjI1)
    apply (cases t)
    unfolding ssbij_def Tmap_def Vmap_def using closed_in_eqvt wf_eqvt by simp
  subgoal
    apply (rule disjI2, rule disjI1)
    apply (erule exE)
    apply (elim conjE)
    subgoal for x
      apply (cases t)
      unfolding ssbij_def Tmap_def Vmap_def using wf_eqvt by auto
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
      apply (auto simp: in_context_eqvt supp_inv_bound typ.rrename_comps typ.rrename_comp0s Ty_eqvt)
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
      apply (cases t) unfolding ssbij_def Tmap_def Vmap_def
      by (auto simp: in_context_eqvt dalist.map_comp supp_inv_bound
          typ.rrename_comps typ.rrename_comp0s dalist.map_id Ty_eqvt)
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
    apply (auto simp: in_context_eqvt supp_inv_bound typ.FFVars_rrenames
          typ.rrename_comps typ.rrename_comp0s extend_eqvt[symmetric] wf_eqvt Ty_eqvt
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

lemma wf_FFVars: "\<turnstile> \<Gamma> ok \<Longrightarrow> a \<in> \<Union>(FFVars_typ ` snd ` set \<Gamma>) \<Longrightarrow> a \<in> dom \<Gamma>"
proof (induction \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case by auto
qed auto

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
     apply auto[1]
     apply (rule iffD2[OF arg_cong3[OF _ refl refl, of _ _ Ty], rotated])
      apply (rule Ty_eqvt)
        apply assumption
       apply (rule bij_swap)
      apply (rule supp_swap_bound)
    apply (rule infinite_var)
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
        apply (metis fst_conv image_eqI list.discI list.inject wf_Ty.cases wf_context)
       apply (drule wf_FFVars[rotated])
        apply (erule wf_context)
       apply (metis fst_conv fun_upd_apply id_apply list.discI list.inject wf_Ty.cases wf_context)
      apply simp
     apply (smt (verit) Prelim.bij_swap fst_conv fun_upd_apply id_apply infinite_var list.discI list.inject subset_eq supp_swap_bound typ.rrename_cong_ids well_scoped(1) wf_Ty.cases wf_context)
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
        apply (metis fst_conv image_eqI list.discI list.inject wf_Ty.cases wf_context)
       apply (drule wf_FFVars[rotated])
        apply (erule wf_context)
       apply (metis fst_conv fun_upd_apply id_apply list.discI list.inject wf_Ty.cases wf_context)
      apply simp
     apply (smt (verit) Prelim.bij_swap fst_conv fun_upd_apply id_apply infinite_var list.discI list.inject subset_eq supp_swap_bound typ.rrename_cong_ids well_scoped(1) wf_Ty.cases wf_context)
    done
  done

interpretation Induct where dummy = "undefined :: var"
  and Tmap = Tmap and Tfvars = Tfvars and Vmap = Vmap and Vfvars = Vfvars and G = G
  apply standard
  using GG_mono GG_equiv GG_fresh by auto
print_theorems

lemma Ty_I: "Ty \<Gamma> T1 T2 = I (\<Gamma>, T1, T2)"
  apply (rule iffI)
  subgoal
   apply (induction \<Gamma> T1 T2 rule: Ty.induct)
        apply (rule I.intros)
        apply (unfold G_def)[1]
        apply (rule disjI1)
        apply simp
       apply (rule I.intros)
       apply (unfold G_def)[1]
       apply (rule disjI2, rule disjI1)
       apply auto[1]
      apply (rule I.intros)
      apply (unfold G_def)[1]
      apply (rule disjI2, rule disjI2, rule disjI1)
      apply auto[1]
          apply (rule I.intros)
      apply (unfold G_def)[1]
     apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
     apply auto[1]
              apply (rule I.intros)
      apply (unfold G_def)[1]
    apply (rule disjI2)+
    by fastforce

    apply (erule I.induct[of "(\<Gamma>, T1, T2)" "\<lambda>(\<Gamma>, T1, T2). \<Gamma> \<turnstile> T1 <: T2", unfolded prod.case])
  subgoal for v t
    apply (cases t)
    apply hypsubst_thin
    apply (unfold prod.case G_def)
    apply (elim disjE)
    by auto
  done

corollary Ty_strong_induct[consumes 1, case_names Bound SA_Top SA_Refl_TVar SA_Trans_TVar SA_Arrow SA_All]:
  "\<Gamma> \<turnstile> S <: T \<Longrightarrow>
  \<forall>\<rho>. |K \<rho>| <o |UNIV::var set| \<Longrightarrow>
  (\<And>\<Gamma> S \<rho>. \<lbrakk> \<turnstile> \<Gamma> ok ; S closed_in \<Gamma> \<rbrakk> \<Longrightarrow> P \<Gamma> S Top \<rho>) \<Longrightarrow>
  (\<And>\<Gamma> x \<rho>. \<lbrakk> \<turnstile> \<Gamma> ok ; TyVar x closed_in \<Gamma> \<rbrakk> \<Longrightarrow> P \<Gamma> (TyVar x) (TyVar x) \<rho>) \<Longrightarrow>
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

lemma Ty_refl: "\<lbrakk> \<turnstile> \<Gamma> ok ; T closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> T <: T"
proof (binder_induction T arbitrary: \<Gamma> avoiding: "dom \<Gamma>" rule: typ.strong_induct)
  case (TyVar x \<Gamma>)
  then show ?case by blast
qed (auto simp: Diff_single_insert SA_All wf_Cons)

lemma Ty_permute: "\<lbrakk> \<Gamma> \<turnstile> S <: T ; \<turnstile> \<Delta> ok ; set \<Gamma> = set \<Delta> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> S <: T"
proof (binder_induction \<Gamma> S T arbitrary: \<Delta> avoiding: "dom \<Delta>" rule: Ty_strong_induct)
  case (SA_Refl_TVar \<Gamma> x \<Delta>)
  then show ?case by blast
next
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 \<Delta>)
  then have "set (\<Gamma>, x <: T\<^sub>1) = set (\<Delta>, x <: T\<^sub>1)" by auto
  then show ?case by (meson SA_All(1,3,5,6,7) Ty.SA_All well_scoped(1) wf_Cons)
qed auto

lemma wf_concat: "\<lbrakk> \<turnstile> \<Delta> ok ; \<turnstile> \<Gamma> ok ; dom \<Gamma> \<inter> dom \<Delta> = {} \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>,\<Delta> ok"
proof (induction \<Delta> rule: wf_Ty.induct)
  case (wf_Cons x \<Delta> T)
  then have 1: "(\<Gamma>, (\<Delta> , x <: T)) = ((\<Gamma>, \<Delta>), x <: T)" by simp
  show ?case unfolding 1
    apply (rule wf_Ty.wf_Cons)
    using wf_Cons by auto
qed auto

lemma weaken_closed: "\<lbrakk> S closed_in \<Gamma> ; dom \<Gamma> \<inter> dom \<Delta> = {} \<rbrakk> \<Longrightarrow> S closed_in \<Gamma>,\<Delta>"
  by auto

lemma Ty_weakening: "\<lbrakk> \<Gamma> \<turnstile> S <: T ; \<turnstile> \<Delta> ok ; dom \<Gamma> \<inter> dom \<Delta> = {} \<rbrakk> \<Longrightarrow> \<Gamma>,\<Delta> \<turnstile> S <: T"
proof (binder_induction \<Gamma> S T avoiding: "dom \<Delta>" rule: Ty_strong_induct)
  case (SA_Top \<Gamma> S)
  then show ?case using wf_concat Ty.SA_Top weaken_closed by presburger
next
  case (SA_Refl_TVar \<Gamma> x)
  then show ?case using wf_concat Ty.SA_Refl_TVar weaken_closed by presburger
next
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2)
  then have "\<turnstile> (\<Gamma>, \<Delta>), x <: T\<^sub>1 ok"
    by (smt (verit) UnE fst_conv image_iff list.discI list.inject set_append well_scoped(1) wf_Cons wf_Ty.cases wf_context)
  then have "(\<Gamma> , \<Delta>), x <: T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2" using Ty_permute SA_All by auto
  then show ?case using SA_All by auto
qed auto

lemma wf_concat_disjoint: "\<turnstile> \<Gamma>, \<Delta> ok \<Longrightarrow> dom \<Gamma> \<inter> dom \<Delta> = {}"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then show ?case
    by (smt (verit, del_insts) Un_iff append_Cons disjoint_iff fst_conv image_iff inf.idem insertE list.inject list.simps(15) set_append set_empty2 wf_Ty.cases)
qed simp

lemma wf_concatD: "\<turnstile> \<Gamma>, \<Delta> ok \<Longrightarrow> \<turnstile> \<Gamma> ok"
  by (induction \<Delta>) auto

lemma narrow_wf: "\<lbrakk> \<turnstile> (\<Gamma> , X <: Q), \<Delta> ok ; R closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> (\<Gamma>, X <: R), \<Delta> ok"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then have "\<turnstile> \<Gamma>, X <: R, \<Delta> ok" by auto
  obtain b c where 2: "a = (b, c)" by fastforce
  then have 1: "\<And>R. \<Gamma> , X <: R, (a # \<Delta>) = (b, c) # (\<Gamma> , X <: R, \<Delta>)" by simp
  have "b \<notin> POPLmark_1A.dom (\<Gamma> , X <: R, \<Delta>)" using Cons(2)[unfolded 1] by auto
  then show ?case unfolding 1 using Cons 2 by auto
qed auto

lemma Ty_transitivity : "\<lbrakk> \<Gamma> \<turnstile> S <: Q ; \<Gamma> \<turnstile> Q <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  and Ty_narrowing : "\<lbrakk> (\<Gamma> , X <: Q), \<Delta> \<turnstile> M <: N ; \<Gamma> \<turnstile> R <: Q \<rbrakk> \<Longrightarrow> (\<Gamma>, X <: R) , \<Delta> \<turnstile> M <: N"
proof (binder_induction Q arbitrary: \<Gamma> \<Delta> avoiding: "dom \<Gamma>" "dom \<Delta>" rule: typ.strong_induct)
  case (TyVar Y \<Gamma> \<Delta>)
  show trans: "\<Gamma> \<turnstile> S <: TyVar Y \<Longrightarrow> \<Gamma> \<turnstile> TyVar Y <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
    by (induction \<Gamma> S "TyVar Y" rule: Ty.induct) auto
  {
    case 2
    then have wf: "\<turnstile> \<Gamma> , X <: R, \<Delta> ok" using narrow_wf well_scoped wf_context by metis
    from 2 have closed: "M closed_in \<Gamma> , X <: R, \<Delta>" "N closed_in \<Gamma> , X <: R, \<Delta>" using well_scoped by fastforce+
    from 2 wf closed show ?case
    proof (binder_induction "\<Gamma>, X <: TyVar Y, \<Delta>" M N arbitrary: \<Delta> avoiding: X "dom \<Gamma>" "dom \<Delta>" rule: Ty_strong_induct)
      case (SA_Trans_TVar x U T \<Delta>')
      then show ?case sorry
    next
      case (SA_Arrow T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 \<Delta>')
      then show ?case by auto
    next
      case (SA_All T\<^sub>1 S\<^sub>1 Z S\<^sub>2 T\<^sub>2 \<Delta>')
      have 1: "\<turnstile> \<Gamma>, X <: R, \<Delta>', Z <: T\<^sub>1 ok"
        apply (rule wf_Cons)
        using SA_All UnI1 image_iff by auto
      have "\<Gamma> , X <: R, (\<Delta>', Z <: T\<^sub>1) \<turnstile> S\<^sub>2 <: T\<^sub>2"
        apply (rule SA_All(5))
        using 1 SA_All(6,8,9) by (auto intro!: SA_All(5))
      then show ?case using SA_All by auto
    qed (rule context_set_bd_UNIV | blast)+
  }
next
  case (Top \<Gamma> \<Delta>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Fun x1 x2 \<Gamma> \<Delta>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Forall x1 x2 x3 \<Gamma> \<Delta>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
qed simp_all




end