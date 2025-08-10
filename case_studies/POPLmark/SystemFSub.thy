(* System F with Subtyping  *)
theory SystemFSub
  imports "Binders.MRBNF_Recursor"
    "Case_Studies.FixedCountableVars"
    "Case_Studies.Generic_Barendregt_Enhanced_Rule_Induction"
    "Labeled_FSet"
begin

declare supp_id_bound[simp]

type_synonym label = string

declare [[mrbnf_internals]]
binder_datatype 'a "typ" =
    TyVar 'a
  | Top
  | Fun "'a typ" "'a typ"
  | Forall \<alpha>::'a "'a typ" t::"'a typ" binds \<alpha> in t
  | TRec "(label, 'a typ) lfset"

declare supp_swap_bound[OF cinfinite_imp_infinite[OF typ.UNIV_cinfinite], simp]
declare typ.permute_id[simp] typ.permute_id0[simp]

lemma Forall_rrename:
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|" shows "
 (\<And>a'. a'\<in>FVars_typ T2 - {x::'a::var} \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> Forall x T1 T2 = Forall (\<sigma> x) T1 (permute_typ \<sigma> T2)"
  apply (unfold Forall_def)
  apply (unfold typ.TT_inject0)
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

lemma Forall_swapD: "Forall (x::'a::var) T1 T2 = Forall y T1' T2' \<Longrightarrow> T1 = T1' \<and> T2' = permute_typ (x \<leftrightarrow> y) T2"
  unfolding typ.inject
  by (auto intro!: typ.permute_cong simp: id_on_def)

type_synonym ('a, 'b) \<Gamma> = "('b \<times> 'a typ) list"
type_synonym 'a \<Gamma>\<^sub>\<tau> = "('a, 'a) \<Gamma>"

definition map_context :: "('a::var \<Rightarrow> 'a) \<Rightarrow> 'a \<Gamma>\<^sub>\<tau> \<Rightarrow> 'a \<Gamma>\<^sub>\<tau>" where
  "map_context f \<equiv> map (map_prod f (permute_typ f))"
abbreviation FFVars_ctxt :: "('a::var, 'b) \<Gamma> \<Rightarrow> 'a set" where
  "FFVars_ctxt xs \<equiv> \<Union>(FVars_typ ` snd ` set xs)"
abbreviation extend :: "('a, 'b) \<Gamma> \<Rightarrow> 'b \<Rightarrow> 'a typ \<Rightarrow> ('a, 'b) \<Gamma>" ("_ \<^bold>, _ <: _" [57,75,75] 71) where
  "extend \<Gamma> x T \<equiv> (x, T)#\<Gamma>"
abbreviation concat :: "('a, 'b) \<Gamma> \<Rightarrow> ('a, 'b) \<Gamma> \<Rightarrow> ('a, 'b) \<Gamma>" (infixl "(\<^bold>,)" 71) where
  "concat \<Gamma> \<Delta> \<equiv> \<Delta> @ \<Gamma>"
abbreviation empty_context :: "('a, 'b) \<Gamma>" ("\<emptyset>") where "empty_context \<equiv> []"
abbreviation dom :: "('a, 'b) \<Gamma> \<Rightarrow> 'b set" where "dom xs \<equiv> fst ` set xs"
abbreviation disjoint :: "('a, 'b) \<Gamma> \<Rightarrow> ('a, 'b) \<Gamma> \<Rightarrow> bool" (infixl "(\<bottom>)" 71) where
  "disjoint \<Gamma> \<Delta> \<equiv> dom \<Gamma> \<inter> dom \<Delta> = {}"

lemma map_context_id[simp]: "map_context id = id"
  unfolding map_context_def by simp
lemma map_context_comp0[simp]:
  assumes "bij (f::'a \<Rightarrow> 'a)" "|supp f| <o |UNIV::'a::var set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "map_context f \<circ> map_context g = map_context (f \<circ> g)"
  apply (rule ext)
  unfolding map_context_def
  using assms by (auto simp: typ.permute_comp)
lemmas map_context_comp = trans[OF comp_apply[symmetric] fun_cong[OF map_context_comp0]]
declare map_context_comp[simp]
lemma context_dom_set[simp]:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "dom (map_context f xs) = f ` dom xs"
  unfolding map_context_def by force
lemma set_bd_UNIV: "|set xs| <o |UNIV::'a::var set|"
  apply (rule ordLess_ordLeq_trans)
   apply (rule list.set_bd)
  apply (rule typ_pre.var_large)
  done
lemma context_set_bd_UNIV[simp]: "|dom xs| <o |UNIV::'a::var set|"
  apply (rule ordLeq_ordLess_trans[OF card_of_image])
  by (simp add: infinite_UNIV)
lemma context_map_cong_id:
  assumes "bij (f::'a \<Rightarrow> 'a)" "|supp f| <o |UNIV::'a::var set|"
  and "\<And>a. a \<in> dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<Longrightarrow> f a = a"
shows "map_context f \<Gamma> = \<Gamma>"
  unfolding map_context_def
  apply (rule trans)
   apply (rule list.map_cong0[of _ _ id])
   apply (rule trans)
    apply (rule prod.map_cong0[of _ _ id _ id])
  using assms by (fastforce intro!: typ.permute_cong_id)+

notation Fun (infixr "\<rightarrow>" 65)
notation Forall ("\<forall> _ <: _ . _" [62, 62, 62] 70)

abbreviation in_context :: "'a \<Rightarrow> 'a typ \<Rightarrow> 'a \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ <: _ \<in> _" [55,55,55] 60) where
  "x <: t \<in> \<Gamma> \<equiv> (x, t) \<in> set \<Gamma>"
abbreviation well_scoped :: "'a::var typ \<Rightarrow> 'a \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("_ closed'_in _" [55, 55] 60) where
  "well_scoped S \<Gamma> \<equiv> FVars_typ S \<subseteq> dom \<Gamma>"

inductive wf_ty :: "'a::var \<Gamma>\<^sub>\<tau> \<Rightarrow> bool" ("\<turnstile> _ ok" [70] 100) where
  wf_Nil[intro]: "\<turnstile> [] ok"
| wf_Cons[intro!]: "\<lbrakk> x \<notin> dom \<Gamma> ; T closed_in \<Gamma> ; \<turnstile> \<Gamma> ok \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>\<^bold>,x<:T ok"

inductive_cases
  wfE[elim]: "\<turnstile> \<Gamma> ok"
  and wf_ConsE[elim!]: "\<turnstile> (a#\<Gamma>) ok"

lemma in_context_eqvt:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "x <: T \<in> \<Gamma> \<Longrightarrow> f x <: permute_typ f T \<in> map_context f \<Gamma>"
  using assms unfolding map_context_def by auto

lemma extend_eqvt:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "map_context f (\<Gamma>\<^bold>,x<:T) = map_context f \<Gamma>\<^bold>, f x <: permute_typ f T"
  unfolding map_context_def by simp

lemma extend_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "bij f2"
  shows "map (map_prod f1 (permute_typ f2)) (\<Gamma>\<^bold>,x<:T) = map (map_prod f1 (permute_typ f2)) \<Gamma>\<^bold>, f1 x <: permute_typ f2 T"
  by simp

lemma closed_in_eqvt:
  assumes "bij (f::'a \<Rightarrow> 'a)" "|supp f| <o |UNIV::'a::var set|"
  shows "S closed_in \<Gamma> \<Longrightarrow> permute_typ f S closed_in map_context f \<Gamma>"
  using assms  by (auto simp: typ.FVars_permute)

lemma wf_eqvt:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "\<turnstile> \<Gamma> ok \<Longrightarrow> \<turnstile> map_context f \<Gamma> ok"
unfolding map_context_def proof (induction \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case using assms apply (auto simp: bij_implies_inject)
     apply (metis fst_conv image_iff)
    by (metis (no_types, lifting) closed_in_eqvt list.set_map map_context_def subsetD)
qed simp

abbreviation Tsupp :: "'a::var \<Gamma>\<^sub>\<tau> \<Rightarrow> 'a typ \<Rightarrow> 'a typ \<Rightarrow> 'a set" where
  "Tsupp \<Gamma> T\<^sub>1 T\<^sub>2 \<equiv> dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<union> FVars_typ T\<^sub>1 \<union> FVars_typ T\<^sub>2"

lemma small_Tsupp: "small (Tsupp x1 x2 x3)"
  by (auto simp: small_def typ.set_bd_UNIV typ.Un_bound var_class.UN_bound set_bd_UNIV typ.set_bd)

lemma fresh: "\<exists>xx. xx \<notin> Tsupp x1 x2 x3"
  using exists_fresh small_Tsupp small_def by blast

lemma swap_idemp[simp]: "id(x := x) = id" by auto
lemma swap_left: "(id(x := xx, xx := x)) x = xx" by simp

lemma wf_FFVars: "\<turnstile> \<Gamma> ok \<Longrightarrow> a \<in> FFVars_ctxt \<Gamma> \<Longrightarrow> a \<in> dom \<Gamma>"
  by (induction \<Gamma>) auto

lemma finite_Tsupp: "finite (Tsupp x1 x2 x3)"
  using finite_iff_ordLess_natLeq typ.set_bd by fastforce

lemma exists_fresh:
"\<exists> z. z \<notin> set xs \<and> z \<notin> Tsupp x1 x2 x3"
proof-
  have 0: "|set xs \<union> Tsupp x1 x2 x3| <o |UNIV::'a::var set|"
    using lfset.Un_bound set_bd_UNIV small_Tsupp small_def by blast
  then obtain x where "x \<notin> set xs \<union> Tsupp x1 x2 x3"
  by (meson exists_fresh)
  thus ?thesis by auto
qed

lemma rrename_swap_FFvars[simp]: "x \<notin> FVars_typ T \<Longrightarrow> xx \<notin> FVars_typ T \<Longrightarrow>
  permute_typ (x \<leftrightarrow> xx) T = T"
apply(rule typ.permute_cong_id) apply auto by (metis swap_def)

lemma map_context_swap_FFVars[simp]:
"\<forall>k\<in>set \<Gamma>. x \<noteq> fst k \<and> x \<notin> FVars_typ (snd k) \<and>
           xx \<noteq> fst k \<and> xx \<notin> FVars_typ (snd k) \<Longrightarrow>
    map_context (x \<leftrightarrow> xx) \<Gamma> = \<Gamma>"
  unfolding map_context_def apply(rule map_idI) by auto

lemma isPerm_swap: "isPerm (x \<leftrightarrow> xx)"
  unfolding isPerm_def by (auto simp: infinite_UNIV)

inductive ty :: "'a::var \<Gamma>\<^sub>\<tau> \<Rightarrow> 'a typ \<Rightarrow> 'a typ \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [55,55,55] 60) where
  SA_Top: "\<lbrakk> \<turnstile> \<Gamma> ok ; S closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_Refl_TVar: "\<lbrakk> \<turnstile> \<Gamma> ok ; TyVar x closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: TyVar x"
| SA_Trans_TVar: "\<lbrakk> x<:U \<in> \<Gamma> ; \<Gamma> \<turnstile> U <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyVar x <: T"
| SA_Arrow: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_All: "\<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma>\<^bold>, x<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<forall>x<:S\<^sub>1. S\<^sub>2 <: \<forall>x<:T\<^sub>1 .T\<^sub>2"
| SA_TRec: "\<lbrakk> \<turnstile> \<Gamma> ok; labels Y \<subseteq> labels X;
    \<And>x T. (x, T) \<in>\<in> X \<Longrightarrow> T closed_in \<Gamma> ;
    \<And>x T. (x, T) \<in>\<in> Y \<Longrightarrow> \<exists>S. (x, S) \<in>\<in> X \<and> \<Gamma> \<turnstile> S <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TRec X <: TRec Y"

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
and
  SA_TRecEL: "\<Gamma> \<turnstile> TRec X <: T"
and
  SA_TRecER: "\<Gamma> \<turnstile> T <: TRec X"

lemma wf_context: "\<Gamma> \<turnstile> S <: T \<Longrightarrow> \<turnstile> \<Gamma> ok"
  by (induction \<Gamma> S T rule: ty.induct)

lemma well_scoped:
  assumes "\<Gamma> \<turnstile> S <: T"
  shows "S closed_in \<Gamma>" "T closed_in \<Gamma>"
using assms proof (induction \<Gamma> S T rule: ty.induct)
  case (SA_Trans_TVar x U \<Gamma> T)
  {
    case 1 then show ?case using SA_Trans_TVar
      by (metis fst_conv imageI singletonD subsetI typ.set(1))
  next
    case 2 then show ?case using SA_Trans_TVar by simp
  }
next
  case (SA_TRec \<Gamma> Y X)
  {
    case 1
    then show ?case unfolding typ.set
    proof safe
      fix x T
      assume a: "T \<in> values X" "x \<in> FVars_typ T"
      from \<open>T \<in> values X\<close> obtain l where 1: "(l, T) \<in>\<in> X"
        by (meson values_lfin)
      then show "x \<in> dom \<Gamma>" using SA_TRec(3) a by fast
    qed
  next
    case 2
    then show ?case unfolding typ.set
      by (auto dest!: values_lfin SA_TRec(4))
  }
qed auto

declare ty.intros[intro]

lemma ty_fresh_extend: "\<Gamma>\<^bold>, x <: U \<turnstile> S <: T \<Longrightarrow> x \<notin> dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<and> x \<notin> FVars_typ U"
  by (metis (no_types, lifting) UnE fst_conv snd_conv subsetD wf_ConsE wf_FFVars wf_context)

lemmas [equiv] = wf_eqvt[unfolded map_context_def] lfin_equiv
  closed_in_eqvt[unfolded map_context_def] in_context_eqvt[unfolded map_context_def]

lemma typ_inject: "Forall x T1 T2 = Forall y R1 R2 \<longleftrightarrow> T1 = R1 \<and> (\<exists>f. bij (f::'a::var \<Rightarrow> 'a) \<and> |supp f| <o |UNIV::'a set| \<and> id_on (FVars_typ T2 - {x}) f \<and> f x = y \<and> permute_typ f T2 = R2)"
  by (smt (z3) Forall_rrename Swapping.bij_swap Swapping.supp_swap_bound id_on_def id_on_swap infinite_UNIV swap_simps(1) typ.inject(3))

lemmas typ.inject(3)[simp del]
binder_inductive ty
  subgoal premises prems for R B \<Gamma> T1 T2
    by (tactic \<open>refreshability_tac false
      [@{term "\<lambda>(\<Gamma>::('a::var \<times> 'a typ) list). dom \<Gamma> \<union> FFVars_ctxt \<Gamma>"}, @{term "FVars_typ :: 'a typ \<Rightarrow> 'a::var set"}, @{term "FVars_typ :: 'a::var typ \<Rightarrow> 'a::var set"}]
      [@{term "permute_typ :: ('a::var \<Rightarrow> 'a) \<Rightarrow> 'a typ \<Rightarrow> 'a typ"}, @{term "(\<lambda>f x. f x) :: ('a::var \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"}]
      [NONE, NONE, NONE, NONE, SOME [NONE, NONE, NONE, SOME 1, SOME 0, SOME 0], NONE]
      @{thm prems(3)} @{thm prems(2)} @{thms prems(1)[THEN ty_fresh_extend] id_onD}
      @{thms emp_bound insert_bound_UNIV ID.set_bd typ.Un_bound typ.UN_bound typ.set_bd_UNIV infinite_UNIV}
      @{thms typ_inject image_iff} @{thms typ.permute_cong_id context_map_cong_id map_idI}
      @{thms cong[OF cong[OF cong[OF refl[of R]] refl] refl, THEN iffD1, rotated -1] id_onD} @{context}\<close>)
  done

lemmas FVars_tvsubst_typ = typ.Vrs_Sb

lemmas [simp] = typ.Vrs_Inj

lemma inj_TyVar[simp, intro!]: "inj TyVar"
  by (meson injI typ.inject(1))

thm IImsupp_Inj_comp_bound1[of TyVar]

lemmas tvsubst_typ_TyVar[simp] = typ.Sb_Inj[THEN fun_cong, unfolded id_apply]

lemma finite_FVars_typ[simp]:"finite (FVars_typ T)"
  by (induct T) auto

end
