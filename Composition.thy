theory Composition
  imports "thys/MRBNF_Composition"
begin

declare [[mrbnf_internals]]

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

(*
binder_datatype 'var \<tau> =
  | TyVar 'var
  | TyArrow
  | TyApp "'var \<tau>" "'var \<tau>"
  | TyForall a::"'var" \<kappa> t::"'var \<tau>" binds a in t

  \<down>

  'tyvar
+ unit
+ 'rec * 'rec
+ 'btyvar * \<kappa> * 'body
*)

declare [[ML_print_depth=10000000]]
local_setup \<open>fn lthy =>
let
  val systemf_type_name = "\<tau>_pre"
  val systemf_type = @{typ "'tyvar + unit + 'rec * 'rec + 'btyvar * \<kappa> * 'body"}
  val Xs = []
  val resBs = map dest_TFree [@{typ 'tyvar}, @{typ 'btyvar}, @{typ 'body}, @{typ 'rec}]
  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (systemf_type_name ^ "_")

  val ((mrbnf, tys), (accum, lthy')) = MRBNF_Comp.mrbnf_of_typ false MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var)] systemf_type
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf, (Ds, info)), lthy'') = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name systemf_type_name) true (fst tys) [] mrbnf lthy'
  val (bnf, lthy''') = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy''
in lthy''' end
\<close>
print_theorems
print_bnfs

ML \<open>
val tau = the (MRBNF_Def.mrbnf_of @{context} "Composition.\<tau>_pre")
\<close>

ML_file \<open>Tools/mrbnf_fp_tactics.ML\<close>
ML_file \<open>Tools/mrbnf_fp.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 1;
\<close>

local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Fp.construct_binder_fp MRBNF_Util.Least_FP
    [(("\<tau>", tau), 2)] [[0]] lthy
in
  lthy'
end
\<close>
print_theorems

term "\<tau>_ctor"

lemma infinite_var_\<tau>_pre: "infinite (UNIV :: 'a::var_\<tau>_pre set)"
  using card_of_ordLeq_finite cinfinite_def infinite_regular_card_order.Cinfinite infinite_regular_card_order_card_suc natLeq_Card_order natLeq_card_order natLeq_cinfinite var_DEADID_class.large by blast

lemma Un_bound:
  assumes inf: "infinite (UNIV :: 'a set)"
    and "|A1| <o |UNIV::'a set|" and "|A2| <o |UNIV::'a set|"
  shows "|A1 \<union> A2| <o |UNIV::'a set|"
  using assms card_of_Un_ordLess_infinite by blast

lemma imsupp_supp_bound: "infinite (UNIV::'a set) \<Longrightarrow> |imsupp g| <o |UNIV::'a set| \<longleftrightarrow> |supp g| <o |UNIV::'a set|"
  by (metis Un_bound card_of_image imsupp_def ordLeq_ordLess_trans supp_ordleq_imsupp)

(******************** Definitions for variable-for-variable substitution ***********)
typedef 'a :: var_\<tau>_pre ssfun = "{f :: 'a \<Rightarrow> 'a. |supp f| <o |UNIV::'a set|}"
  by (auto intro!: exI[of _ id] simp: supp_id_bound)

setup_lifting type_definition_ssfun

lift_definition idSS :: "'a ::var_\<tau>_pre ssfun" is id
  by (simp add: supp_id_bound)

lemma supp_comp_bound_var_\<tau>_pre: "\<lbrakk> |supp f| <o |UNIV::'a::var_\<tau>_pre set| ; |supp g| <o |UNIV::'a set| \<rbrakk> \<Longrightarrow> |supp (g \<circ> f)| <o |UNIV::'a set|"
  using infinite_var_\<tau>_pre supp_comp_bound by blast

context
  fixes u :: "'a :: var_\<tau>_pre \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o |UNIV::'a set|"
begin
  lift_definition compSS :: "'a ::var_\<tau>_pre ssfun \<Rightarrow> 'a ssfun" is "\<lambda>p. u o p o inv u"
    by (simp add: supp_comp_bound_var_\<tau>_pre supp_inv_bound u)
end

lemma compSS_id: "compSS id = id"
  supply supp_id_bound[transfer_rule] bij_id[transfer_rule] by (rule ext, transfer) auto
lemma compSS_comp:
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a" and g :: "'a \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "compSS (f \<circ> g) = compSS f \<circ> compSS g"
  supply assms[transfer_rule] bij_comp[transfer_rule] supp_comp_bound_var_\<tau>_pre[transfer_rule]
  by (rule ext, transfer) (auto simp: fun_eq_iff assms o_inv_distrib)
lemma compSS_cong_id:
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a" and d :: "'a ssfun"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "\<And>a. a \<in> imsupp (Rep_ssfun d) \<Longrightarrow> f a = a"
  shows "compSS f d = d"
  supply assms(1,2)[transfer_rule]
  using assms(3)
  apply transfer
  subgoal for d
    unfolding fun_eq_iff o_apply
    apply (subst imsupp_commute[of f d, unfolded fun_eq_iff o_apply, rule_format])
    apply (auto simp: assms(1) image_iff imsupp_def supp_def)
    apply (meson assms(1) bij_implies_inject)
    by (metis assms(1) bij_pointE)
  done
lemma imsupp_ssfun_bound:
  fixes p :: "'a::var_\<tau>_pre ssfun"
  shows "|imsupp (Rep_ssfun p)| <o |UNIV::'a set|"
  unfolding imsupp_def
  apply (rule card_of_Un_ordLess_infinite)
    apply (rule infinite_var_\<tau>_pre)
  using Rep_ssfun apply blast
  by (metis Rep_ssfun card_of_image mem_Collect_eq ordLeq_ordLess_trans)
lemma in_PFVars_Pmap':
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "f a \<in> imsupp (Rep_ssfun (compSS f d)) \<longleftrightarrow> a \<in> imsupp (Rep_ssfun d)"
proof
  assume a: "f a \<in> imsupp (Rep_ssfun (compSS f d))"
  show "a \<in> imsupp (Rep_ssfun d)"
    supply assms[transfer_rule]
    using a apply transfer
    by (auto simp: supp_def imsupp_def image_iff assms(1) bij_inv_eq_iff[of f, symmetric])
next
  assume a: "a \<in> imsupp (Rep_ssfun d)"
  show "f a \<in> imsupp (Rep_ssfun (compSS f d))"
    supply assms[transfer_rule]
    using a apply transfer
    by (auto simp: supp_def imsupp_def image_iff assms(1) intro: exI[of _ "f _"])
qed
corollary in_PFVars_Pmap:
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "a \<in> imsupp (Rep_ssfun (compSS f d)) \<longleftrightarrow> inv f a \<in> imsupp (Rep_ssfun d)"
  using in_PFVars_Pmap' assms inv_simp2 by metis

typedef 'a U = "{ x::'a \<tau>. True }"
  by simp
print_theorems
lemmas Abs_U_inverse = Abs_U_inverse[OF UNIV_I[unfolded UNIV_def]]

definition CCTOR' :: "('a::var_\<tau>_pre, 'a, 'a ssfun \<Rightarrow> 'a \<tau>, 'a ssfun \<Rightarrow> 'a \<tau>) \<tau>_pre \<Rightarrow> 'a ssfun \<Rightarrow> 'a \<tau>" where
  "CCTOR' \<equiv> \<lambda>F p. \<tau>_ctor (map_\<tau>_pre (Rep_ssfun p) id (\<lambda>R. R p) (\<lambda>R. R p) F)"
definition CCTOR :: "('a::var_\<tau>_pre, 'a, 'a \<tau> \<times> ('a ssfun \<Rightarrow> 'a U), 'a \<tau> \<times> ('a ssfun \<Rightarrow> 'a U)) \<tau>_pre \<Rightarrow> 'a ssfun \<Rightarrow> 'a U" where
  "CCTOR = (\<lambda>F p. Abs_U (\<tau>_ctor (map_\<tau>_pre (Rep_ssfun p) id ((\<lambda>R. Rep_U (R p)) o snd) ((\<lambda>R. Rep_U (R p)) o snd) F)))"
definition Umap :: "('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> 'a \<tau> \<Rightarrow> 'a U \<Rightarrow> 'a U" where
  "Umap f t x \<equiv> Abs_U (rrename_\<tau> f (Rep_U x))"
definition UFVars :: "'a::var_\<tau>_pre \<tau> \<Rightarrow> 'a U \<Rightarrow> 'a set" where
  "UFVars t x \<equiv> FFVars_\<tau> (Rep_U x)"
definition AS :: "'a::var_\<tau>_pre set" where "AS = {}"

lemma Umap_id0: "Umap id t = id"
  unfolding Umap_def \<tau>.rrename_id0s
  unfolding id_apply Rep_U_inverse
  by (rule refl)
lemma Umap_comp0:
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a" and g :: "'a \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "Umap (g \<circ> f) t = Umap g t \<circ> Umap f t"
  unfolding Umap_def comp_def Abs_U_inverse
  unfolding arg_cong[OF \<tau>.rrename_comps[symmetric, unfolded comp_def, OF assms], of Abs_U]
  by (rule refl)
lemma Umap_cong_id:
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "\<And>z. z \<in> UFVars t w \<Longrightarrow> f z = z"
  shows "Umap f t w = w"
  apply (rule trans)
  unfolding Umap_def
   apply (rule arg_cong[of _ _ Abs_U])
   apply (rule \<tau>.rrename_cong_ids)
     apply (rule assms)+
  unfolding UFVars_def
   apply assumption
  by (rule Rep_U_inverse)

lemma UFVars_subset: "set2_\<tau>_pre y \<inter> (imsupp (Rep_ssfun p) \<union> AS) = {} \<Longrightarrow>
       (\<And>t pu p. (t, pu) \<in> set3_\<tau>_pre y \<union> set4_\<tau>_pre y \<Longrightarrow> UFVars t (pu p) \<subseteq> FFVars_\<tau> t \<union> imsupp (Rep_ssfun p) \<union> AS) \<Longrightarrow>
       UFVars t (CCTOR y p) \<subseteq> FFVars_\<tau> (\<tau>_ctor (map_\<tau>_pre id id fst fst y)) \<union> imsupp (Rep_ssfun p) \<union> AS"
  unfolding Un_empty_right CCTOR_def UFVars_def
  apply (auto simp: imsupp_supp_bound[OF infinite_var_\<tau>_pre] \<tau>.FFVars_cctors \<tau>_pre.set_map supp_id_bound emp_bound Rep_ssfun[simplified])
  sorry
  (*using imsupp_def supp_def apply fastforce
  using imsupp_def supp_def apply fastforce
  by fastforce+*)

(*lemma UFVars_subset': "set2_\<tau>_pre y \<inter> (imsupp (Rep_ssfun p) \<union> AS) = {} \<Longrightarrow>
   (\<And>pu p. pu \<in> set3_\<tau>_pre y \<Longrightarrow> FFVars_\<tau> (pu p) - set2_\<tau>_pre y \<subseteq> imsupp (Rep_ssfun p) \<union> AS) \<Longrightarrow>
   (\<And>pu p. pu \<in> set4_\<tau>_pre y \<Longrightarrow> FFVars_\<tau> (pu p) \<subseteq> imsupp (Rep_ssfun p) \<union> AS) \<Longrightarrow> FFVars_\<tau> (CCTOR' y p) \<subseteq> set1_\<tau>_pre y \<union> imsupp (Rep_ssfun p) \<union> AS"
  unfolding Un_empty_right CCTOR'_def
  apply (auto simp: imsupp_supp_bound[OF infinite_var_\<tau>_pre] \<tau>.FFVars_cctors \<tau>_pre.set_map supp_id_bound emp_bound Rep_ssfun[simplified])
  using imsupp_def supp_def apply fastforce
  by fastforce*)
lemma in_UFVars_Umap: "bij (f::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> (a \<in> UFVars (rrename_\<tau> f t) (Umap f t d)) = (inv f a \<in> UFVars t d)"
  unfolding Umap_def UFVars_def
  apply (rule trans[OF _ image_in_bij_eq])
   apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
  unfolding Abs_U_inverse
   apply (rule \<tau>.FFVars_rrenames)
  by assumption+

lemma Umap_Uctor: "bij (f::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow>
       |supp f| <o |UNIV::'a set| \<Longrightarrow>
       Umap f (\<tau>_ctor (map_\<tau>_pre id id fst fst y)) (CCTOR y p) =
       CCTOR (map_\<tau>_pre f f (\<lambda>(t, pu). (rrename_\<tau> f t, \<lambda>p. Umap f t (pu (compSS (inv f) p)))) (\<lambda>(t, pu). (rrename_\<tau> f t, \<lambda>p. Umap f t (pu (compSS (inv f) p)))) y) (compSS f p)"
  unfolding Umap_def CCTOR_def sorry
  (*by (auto simp: \<tau>.rrename_id0s \<tau>.rrename_cctors \<tau>_pre.map_comp compSS.rep_eq Rep_ssfun[simplified]
      supp_comp_bound infinite_var_\<tau>_pre supp_inv_bound supp_id_bound inv_o_simp1[THEN rewriteR_comp_comp]
      fun_cong[OF compSS_comp[unfolded comp_def], symmetric] compSS_id[unfolded id_def] Abs_U_inverse Rep_U_inverse
      intro!: \<tau>.cctor_eq_intro_rrenames[of id] \<tau>_pre.map_cong)*)
lemma Umap_Uctor': "bij (f::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> rrename_\<tau> f (CCTOR' y p) = CCTOR' (map_\<tau>_pre f f (\<lambda>pu p. rrename_\<tau> f (pu (compSS (inv f) p))) (\<lambda>pu p. rrename_\<tau> f (pu (compSS (inv f) p))) y) (compSS f p)"
  unfolding CCTOR'_def
  by (auto simp: \<tau>.rrename_id0s \<tau>.rrename_cctors \<tau>_pre.map_comp compSS.rep_eq Rep_ssfun[simplified]
      supp_comp_bound infinite_var_\<tau>_pre supp_inv_bound supp_id_bound inv_o_simp1[THEN rewriteR_comp_comp]
      fun_cong[OF compSS_comp[unfolded comp_def], symmetric] compSS_id[unfolded id_def]
      intro!: \<tau>.cctor_eq_intro_rrenames[of id] \<tau>_pre.map_cong)

abbreviation "mapP \<equiv> compSS"
abbreviation "PFVars \<equiv> \<lambda>p. imsupp (Rep_ssfun p)"
(***************************************************************************************)
ML_file \<open>Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>Tools/mrbnf_recursor.ML\<close>

local_setup \<open>fn lthy =>
let
  fun rtac ctxt = resolve_tac ctxt o single
  val model_tacs = {
    small_avoiding_sets = [fn ctxt => Ctr_Sugar_Tactics.unfold_thms_tac ctxt @{thms AS_def} THEN rtac ctxt @{thm emp_bound} 1],
    Umap_id0 = fn ctxt => resolve_tac ctxt @{thms Umap_id0} 1,
    Umap_comp0 = fn ctxt => EVERY1 [rtac ctxt @{thm Umap_comp0}, REPEAT_DETERM o assume_tac ctxt],
    Umap_cong_ids = map (fn thm => fn ctxt => EVERY1 [
      resolve_tac ctxt [thm],
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]) @{thms Umap_cong_id},
    in_UFVars_Umap = [fn ctxt => EVERY1 [rtac ctxt @{thm in_UFVars_Umap}, REPEAT_DETERM o assume_tac ctxt]],
    Umap_Uctor = fn ctxt => EVERY1 [rtac ctxt @{thm Umap_Uctor}, REPEAT_DETERM o assume_tac ctxt],
    UFVars_subsets = [fn ctxt => EVERY1 [
      rtac ctxt @{thm UFVars_subset},
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]]
  };
  val parameter_tacs = {
    Pmap_id0 = fn ctxt => rtac ctxt @{thm compSS_id} 1,
    Pmap_comp0 = fn ctxt => EVERY1 [rtac ctxt @{thm compSS_comp}, REPEAT_DETERM o assume_tac ctxt],
    Pmap_cong_ids = [fn ctxt => EVERY1 [
      rtac ctxt @{thm compSS_cong_id},
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]],
    in_PFVars_Pmap = [fn ctxt => EVERY1 [rtac ctxt @{thm in_PFVars_Pmap}, REPEAT_DETERM o assume_tac ctxt]],
    small_PFVars = [fn ctxt => rtac ctxt @{thm imsupp_ssfun_bound} 1]
  };
  val model = {
    U = @{typ "'a::var_\<tau>_pre U"},
    term_quotient = {
      qT = @{typ "'a::var_\<tau>_pre \<tau>"},
      qmap = @{term rrename_\<tau>},
      qctor = @{term \<tau>_ctor},
      qFVars = [@{term FFVars_\<tau>}]
    },
    UFVars = [@{term "UFVars"}],
    Umap = @{term "Umap"},
    Uctor = @{term CCTOR},
    avoiding_sets = [@{term AS}],
    mrbnf = tau,
    binding_dispatcher = [[0]],
    parameters = {
      P = @{typ "'a::var_\<tau>_pre ssfun"},
      PFVars = [@{term "\<lambda>p. imsupp (Rep_ssfun p)"}],
      Pmap = @{term "compSS"},
      axioms = parameter_tacs
    },
    axioms = model_tacs
  };
  val lthy' = MRBNF_Recursor.create_binding_recursor model @{binding ff0} lthy
in lthy' end
\<close>
print_theorems

lemma card_of_subset_bound: "\<lbrakk> B \<subseteq> A ; |A| <o x \<rbrakk> \<Longrightarrow> |B| <o x"
  using card_of_mono1 ordLeq_ordLess_trans by blast
lemma card_of_minus_bound: "|A| <o |UNIV::'a set| \<Longrightarrow> |A - B| <o |UNIV::'a set|"
  by (rule card_of_subset_bound[OF Diff_subset])

lemma exists_subset_compl:
  assumes "infinite (UNIV::'b set)" "|U \<union> S::'b set| <o |UNIV::'b set|"
  shows "\<exists>B. U \<inter> B = {} \<and> B \<inter> S = {} \<and> |U| =o |B|"
proof -
  have 1: "|U| <o |UNIV::'b set|" using assms(2) using card_of_Un1 ordLeq_ordLess_trans by blast
  have "|-(U \<union> S)| =o |UNIV::'b set|" using infinite_UNIV_card_of_minus[OF assms(1,2)]
    by (simp add: Compl_eq_Diff_UNIV)
  then have "|U| <o |-(U \<union> S)|" using 1 ordIso_symmetric ordLess_ordIso_trans by blast
  then obtain B where 1: "B \<subseteq> -(U \<union> S)" "|U| =o |B|"
    by (meson internalize_card_of_ordLeq2 ordLess_imp_ordLeq)
  then have "U \<inter> B = {}" "B \<inter> S = {}" by blast+
  then show ?thesis using 1 by blast
qed

lemma exists_suitable_aux:
  assumes "infinite (UNIV::'a set)" "|U \<union> (S - U)::'a set| <o |UNIV::'a set|"
  shows "\<exists>(u::'a \<Rightarrow> 'a). bij u \<and> |supp u| <o |UNIV::'a set| \<and> imsupp u \<inter> (S - U) = {} \<and> u ` U \<inter> S = {}"
proof -
  have 1: "|U| <o |UNIV::'a set|" using assms(2) using card_of_Un1 ordLeq_ordLess_trans by blast
  obtain B where 2: "U \<inter> B = {}" "B \<inter> (S - U) = {}" "|U| =o |B|"
    using exists_subset_compl[OF assms(1,2)] by blast
  obtain u where 3: "bij u" "|supp u| <o |UNIV::'a set|" "bij_betw u U B" "imsupp u \<inter> (S - U) = {}"
    using ordIso_ex_bij_betw_supp[OF assms(1) 1 2(3,1) Diff_disjoint 2(2)] by blast
  then have "u ` U \<subseteq> B" unfolding bij_betw_def by blast
  then have "u ` U \<inter> S = {}" using 2 by blast
  then show ?thesis using 3 by blast
qed

lemma fst_comp_map_prod: "h \<circ> fst = fst \<circ> map_prod h id" by auto

lemma imsupp_same_subset: "\<lbrakk> a \<notin> B ; a \<in> A ; imsupp f \<inter> A \<subseteq> B \<rbrakk> \<Longrightarrow> f a = a"
  unfolding imsupp_def supp_def by blast

lemma arg_cong3: "\<lbrakk> a1 = a2 ; b1 = b2 ; c1 = c2 \<rbrakk> \<Longrightarrow> h a1 b1 c1 = h a2 b2 c2"
  by simp

lemma exists_bij_betw:
  fixes L R::"'a \<Rightarrow> 'a"
  assumes "infinite (UNIV::'a set)" "bij R" "bij L"
    and u: "|f1 (A x) \<union> g (A x)::'a set| <o |UNIV::'a set|" "f1 (A x) \<inter> g (A x) = {}" "f1 (A x) = L ` f2 x"
    and w: "|(f1 (B x)) \<union> (g (B x))::'a set| <o |UNIV::'a set|" "f1 (B x) \<inter> g (B x) = {}" "f1 (B x) = R ` f2 x"
  shows "\<exists>(u::'a \<Rightarrow> 'a) (w::'a \<Rightarrow> 'a).
    bij u \<and> |supp u| <o |UNIV::'a set| \<and> imsupp u \<inter> g (A x) = {} \<and> u ` f1 (A x) \<inter> f1 (A x) = {}
  \<and> bij w \<and> |supp w| <o |UNIV::'a set| \<and> imsupp w \<inter> g (B x) = {} \<and> w ` f1 (B x) \<inter> f1 (B x) = {}
  \<and> eq_on (f2 x) (u \<circ> L) (w \<circ> R)"
proof -
  have 1: "|f1 (A x)| <o |UNIV::'a set|" "|f1 (B x)| <o |UNIV::'a set|"
    using card_of_Un1 card_of_Un2 ordLeq_ordLess_trans u(1) w(1) by blast+
  have "|f1 (A x) \<union> g (A x) \<union> f1 (B x) \<union> g (B x)| <o |UNIV::'a set|" (is "|?A| <o _")
    using card_of_Un_ordLess_infinite[OF assms(1) u(1) w(1)] Un_assoc by metis
  then have "|-?A| =o |UNIV::'a set|"
    by (rule infinite_UNIV_card_of_minus[OF assms(1) _, unfolded Compl_eq_Diff_UNIV[symmetric]])
  then have "|f1 (A x)| <o |-?A|" by (rule ordLess_ordIso_trans[OF 1(1) ordIso_symmetric])
  then obtain C where C: "C \<subseteq> -?A" "|f1 (A x)| =o |C|"
    using ordLess_imp_ordLeq[THEN iffD1[OF internalize_card_of_ordLeq2]] by metis
  then have 3: "f1 (A x) \<inter> C = {}" "C \<inter> g (A x) = {}" "f1 (B x) \<inter> C = {}" "C \<inter> g (B x) = {}" by blast+

  obtain u::"'a \<Rightarrow> 'a" where x: "bij u" "|supp u| <o |UNIV::'a set|" "bij_betw u (f1 (A x)) C" "imsupp u \<inter> g (A x) = {}"
    using ordIso_ex_bij_betw_supp[OF assms(1) 1(1) C(2) 3(1) u(2) 3(2)] by blast

  have "bij_betw (inv R) (f1 (B x)) (f2 x)" unfolding bij_betw_def by (simp add: assms(2) inj_on_def w(3))
  moreover have "bij_betw L (f2 x) (f1 (A x))" unfolding bij_betw_def by (simp add: assms(3) inj_on_def u(3))
  ultimately have 4: "bij_betw (u \<circ> L \<circ> inv R) (f1 (B x)) C" using bij_betw_trans x(3) by blast

  obtain w::"'a \<Rightarrow> 'a" where y: "bij w" "|supp w| <o |UNIV::'a set|" "bij_betw w (f1 (B x)) C"
    "imsupp w \<inter> g (B x) = {}" "eq_on (f1 (B x)) w (u \<circ> L \<circ> inv R)"
    using ex_bij_betw_supp[OF assms(1) 1(2) 4 3(3) w(2) 3(4)] by blast

  have "eq_on (f2 x) (u \<circ> L) (w \<circ> R)" using y(5) unfolding eq_on_def using assms(2) w(3) by auto
  moreover have "u ` f1 (A x) \<inter> f1 (A x) = {}" "w ` f1 (B x) \<inter> f1 (B x) = {}" using bij_betw_imp_surj_on x(3) y(3) 3(1,3) by blast+
  ultimately show ?thesis using x(1,2,4) y(1,2,4) by blast
qed

lemma imsupp_id_on: "imsupp u \<inter> A = {} \<Longrightarrow> id_on A u"
  unfolding imsupp_def supp_def id_on_def by blast

(************************************************************************************)

(* TODO: add somewhere automatically *)
lemma set2_\<tau>_pre_bound: "|set2_\<tau>_pre (x::('a, 'a, _, _) \<tau>_pre)| <o |UNIV::'a::var_\<tau>_pre set|"
  apply (rule ordLess_ordLeq_trans)
   apply (raw_tactic \<open>resolve_tac @{context} (MRBNF_Def.set_bd_of_mrbnf tau) 1\<close>)
  apply (rule ordIso_ordLeq_trans)
   apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
   apply (rule infinite_regular_card_order.Card_order)
   apply (raw_tactic \<open>resolve_tac @{context} [MRBNF_Def.bd_infinite_regular_card_order_of_mrbnf tau] 1\<close>)
  apply (raw_tactic \<open>resolve_tac @{context} [#var_large (MRBNF_Def.class_thms_of_mrbnf tau)] 1\<close>)
  done

(* TODO maybe add on Quotient? *)
lemma rrename_\<tau>_simps: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> rrename_\<tau> u (quot_type.abs alpha_\<tau> Abs_\<tau> x) = quot_type.abs alpha_\<tau> Abs_\<tau> (rename_\<tau> u x)"
  unfolding rrename_\<tau>_def
  apply (rule iffD2[OF \<tau>.TT_Quotient_total_abs_eq_iffs])
  apply (rule iffD2[OF \<tau>.alpha_bij_eqs])
    apply assumption+
  apply (rule \<tau>.TT_Quotient_rep_abss)
  done

definition suitable :: "(('a::var_\<tau>_pre, 'a, 'a raw_\<tau>, 'a raw_\<tau>) \<tau>_pre \<Rightarrow> 'a ssfun \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> bool" where
  "suitable \<equiv> \<lambda>pick. \<forall>x p. bij (pick x p) \<and> |supp (pick x p)| <o |UNIV::'a set| \<and>
    imsupp (pick x p) \<inter> (FVars_\<tau> (raw_\<tau>_ctor x) \<union> imsupp (Rep_ssfun p) \<union> AS - set2_\<tau>_pre x) = {} \<and>
    pick x p ` (set2_\<tau>_pre x) \<inter> (FVars_\<tau> (raw_\<tau>_ctor x) \<union> imsupp (Rep_ssfun p) \<union> AS) = {}"

definition pick0 :: "('a::var_\<tau>_pre, 'a, 'a raw_\<tau>, 'a raw_\<tau>) \<tau>_pre \<Rightarrow> 'a ssfun \<Rightarrow> 'a \<Rightarrow> 'a" where
  "pick0 \<equiv> SOME pick. suitable pick"

lemma exists_suitable: "\<exists>pick. suitable pick"
  unfolding suitable_def
  apply (rule choice allI)+
  apply (rule exists_suitable_aux)
   apply (rule infinite_var_\<tau>_pre)
  apply (rule \<tau>_pre.Un_bound)
   apply (rule set2_\<tau>_pre_bound)
  apply (rule card_of_minus_bound)
  apply (rule \<tau>_pre.Un_bound)
   apply (rule \<tau>_pre.Un_bound)
    apply (rule \<tau>.card_of_FVars_bounds)
   apply (rule ff0.small_PFVars)
  apply (rule ff0.small_avoiding_sets)
  done

lemma suitable_pick0: "suitable pick0"
  unfolding pick0_def by (rule someI_ex[OF exists_suitable])

ML \<open>
val unfold_thms_tac = Ctr_Sugar_Tactics.unfold_thms_tac
fun rtac ctxt = resolve_tac ctxt o single
fun etac ctxt = eresolve_tac ctxt o single

val var_types = MRBNF_Def.var_types_of_mrbnf tau
val rename_t = @{term "rename_\<tau> :: ('a::var_\<tau>_pre => 'a) \<Rightarrow> _ \<Rightarrow> _"}
val vars = [@{typ "'a::var_\<tau>_pre"}]
val raw_T = @{typ "'a::var_\<tau>_pre raw_\<tau>"}
val Pmap_t = @{term "mapP :: ('a::var_\<tau>_pre => 'a) \<Rightarrow> _ \<Rightarrow> _"}
\<close>

lemma pick0_id_on: "id_on (\<Union> (FVars_\<tau> ` set3_\<tau>_pre x) - set2_\<tau>_pre x) (pick0 x p)"
  apply (insert suitable_pick0)
  unfolding suitable_def Int_Un_distrib Un_empty \<tau>.FVars_ctors Un_Diff Diff_idemp
  apply (erule allE conjE)+
  apply (rule imsupp_id_on)
  apply assumption
  done

corollary pick0_id_on_image: "\<And>u x p. bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> id_on (u ` (\<Union> (FVars_\<tau> ` set3_\<tau>_pre x) - set2_\<tau>_pre x)) (pick0 (map_\<tau>_pre u u (rename_\<tau> u) (rename_\<tau> u) x) p)"
  by (raw_tactic \<open>Subgoal.FOCUS (fn {context, prems, params, ...} =>
    let
      val [bij, supp] = prems
      val map_t = MRBNF_Def.mk_map_of_mrbnf [] [raw_T, raw_T] [raw_T, raw_T] vars vars tau
      val [u, x, p] = map (Thm.term_of o snd) params
      val map_ct = Thm.cterm_of context (map_t $ u $ u $ (rename_t $ u) $ (rename_t $ u) $ x)
      val thm = infer_instantiate' context [SOME map_ct] @{thm pick0_id_on}
      val set_map = map (fn thm => thm OF [supp, bij, supp]) (MRBNF_Def.set_map_of_mrbnf tau)
      val thm' = Local_Defs.unfold0 context (
        @{thms image_comp[unfolded comp_def] image_UN[symmetric]} @ set_map
        @ [@{thm \<tau>.FVars_renames} OF [bij, supp], @{thm bij_is_inj[THEN image_set_diff[symmetric]]} OF [bij]]
      ) thm
    in rtac context thm' 1 end
  ) @{context} 1\<close>)

lemma pick0_prems: "bij (pick0 (x::('a::var_\<tau>_pre, 'a, 'a raw_\<tau>, 'a raw_\<tau>) \<tau>_pre) p)" "|supp (pick0 x p)| <o |UNIV::'a set|"
   apply (insert suitable_pick0)
  unfolding suitable_def
   apply ((erule allE conjE)+, assumption)+
  done

lemma imsupp_image_subset: "u ` A \<inter> A = {} \<Longrightarrow> A \<subseteq> imsupp u"
  unfolding imsupp_def supp_def by auto
lemma Int_subset_empty1: "A \<inter> B = {} \<Longrightarrow> C \<subseteq> A \<Longrightarrow> C \<inter> B = {}" by blast
lemma Int_subset_empty2: "A \<inter> B = {} \<Longrightarrow> C \<subseteq> B \<Longrightarrow> A \<inter> C = {}" by blast

lemma Pmap_bij:
  assumes "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a)" "|supp u| <o |UNIV::'a set|"
  shows "bij (mapP u)"
  by (raw_tactic \<open>MRBNF_Fp_Tactics.mk_rename_bij_tac @{thm ff0.Pmap_comp0[symmetric, rotated -2]} @{thm ff0.Pmap_id0} @{context} @{thms assms}\<close>)
lemma Pmap_inv_simp:
  assumes "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a)" "|supp u| <o |UNIV::'a set|"
  shows "inv (mapP u) = mapP (inv u)"
  by (raw_tactic \<open>MRBNF_Fp_Tactics.mk_rename_inv_simp_tac @{thm ff0.Pmap_comp0[symmetric, rotated -2]} @{thm ff0.Pmap_id0} @{context} @{thms assms}\<close>)

definition Umap' :: "('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> 'a raw_\<tau> \<Rightarrow> 'a U \<Rightarrow> 'a U" where
  "Umap' u t x \<equiv> Umap u (quot_type.abs alpha_\<tau> Abs_\<tau> t) x"
definition UFVars' :: "'a::var_\<tau>_pre raw_\<tau> \<Rightarrow> 'a U \<Rightarrow> 'a set" where
  "UFVars' t d \<equiv> UFVars (quot_type.abs alpha_\<tau> Abs_\<tau> t) d"

definition "PUmap u t pu \<equiv> \<lambda>p. Umap u t (pu (mapP (inv u) p))"
definition "PUmap' u t pu \<equiv> \<lambda>p. Umap' u t (pu (mapP (inv u) p))"

definition CTOR :: "('a::var_\<tau>_pre, 'a, 'a raw_\<tau> \<times> ('a ssfun \<Rightarrow> 'a U), 'a raw_\<tau> \<times> ('a ssfun \<Rightarrow> 'a U)) \<tau>_pre \<Rightarrow> 'a ssfun \<Rightarrow> 'a U" where
  "CTOR x \<equiv> CCTOR (map_\<tau>_pre id id (map_prod (quot_type.abs alpha_\<tau> Abs_\<tau>) id) (map_prod (quot_type.abs alpha_\<tau> Abs_\<tau>) id) x)"

lemma Pmap_imsupp_empty: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow>
  imsupp u \<inter> PFVars p = {} \<Longrightarrow> mapP u p = p"
  apply (rule ff0.Pmap_cong_ids)
    apply assumption
  apply assumption
  apply (drule imsupp_id_on)
  unfolding id_on_def
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma Umap'_CTOR: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow>
  Umap' u (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst y)) (CTOR y p) =
  CTOR (map_\<tau>_pre u u (\<lambda>(t, pu). (rename_\<tau> u t, PUmap' u t pu)) (\<lambda>(t, pu). (rename_\<tau> u t, PUmap' u t pu)) y) (mapP u p)"
  unfolding Umap'_def CTOR_def \<tau>.TT_abs_ctors
  apply (rule trans)
   apply (rule arg_cong3[OF refl _ refl, of _ _ Umap])
   apply (rule arg_cong[of _ _ \<tau>_ctor])
   apply (rule trans)
    apply (rule \<tau>_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
  unfolding fst_comp_map_prod
   apply (rule \<tau>_pre.map_comp[THEN sym])
        apply (rule supp_id_bound bij_id)+
  apply (rule trans)
   apply (rule ff0.Umap_Uctor)
    apply assumption+
  apply (rule arg_cong2[OF _ refl, of _ _ CCTOR])
  apply (rule trans)
   apply (rule \<tau>_pre.map_comp)
        apply (rule supp_id_bound bij_id | assumption)+
  apply (rule trans[rotated])
   apply (rule sym)
   apply (rule \<tau>_pre.map_comp)
        apply (rule supp_id_bound bij_id | assumption)+
  unfolding id_o o_id
  apply (rule \<tau>_pre.map_cong)
            apply assumption+
      apply (rule refl)+
  unfolding comp_def case_prod_map_prod split_beta fst_map_prod snd_map_prod map_prod_simp id_apply PUmap'_def Umap'_def
   apply (rule iffD2[OF prod.inject], rule conjI, rule rrename_\<tau>_simps, assumption+, rule refl)+
  done

lemma FVars_\<tau>_def2: "FVars_\<tau> t = FFVars_\<tau> (quot_type.abs alpha_\<tau> Abs_\<tau> t)"
  unfolding FFVars_\<tau>_def
  apply (rule \<tau>.alpha_FVarss)
  apply (rule \<tau>.TT_alpha_quotient_syms)
  done

lemmas id_prems = supp_id_bound bij_id supp_id_bound

lemma exists_map_prod_id: "(a, b) \<in> map_prod f id ` A \<Longrightarrow> \<exists>c. (c, b) \<in> A \<and> a = f c" by auto


lemma UFVars'_CTOR: "set2_\<tau>_pre y \<inter> (PFVars p \<union> AS) = {} \<Longrightarrow>
(\<And>t pu p. (t, pu) \<in> set3_\<tau>_pre y \<union> set4_\<tau>_pre y \<Longrightarrow> UFVars' t (pu p) \<subseteq> FVars_\<tau> t \<union> PFVars p \<union> AS) \<Longrightarrow>
UFVars' t (CTOR y p) \<subseteq> FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst y)) \<union> PFVars p \<union> AS"
  unfolding UFVars'_def CTOR_def FVars_\<tau>_def2 \<tau>.TT_abs_ctors \<tau>_pre.map_comp[OF id_prems id_prems] fst_comp_map_prod
  unfolding \<tau>_pre.map_comp[OF id_prems id_prems, symmetric]
  apply (rule ff0.UFVars_subsets)
  unfolding \<tau>_pre.set_map[OF id_prems] image_id image_Un[symmetric]
   apply assumption
   apply (drule exists_map_prod_id, (erule exE conjE)+,
      raw_tactic \<open>hyp_subst_tac @{context} 1 THEN Goal.assume_rule_tac @{context} 1\<close>)+
  done

lemma Umap'_cong_ids: "bij (f::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> (\<And>a. a \<in> UFVars' t d \<Longrightarrow> f a = a) \<Longrightarrow> Umap' f t d = d"
  unfolding UFVars'_def Umap'_def
  apply (rule ff0.Umap_cong_ids)
    apply assumption
   apply assumption
  apply (raw_tactic \<open>Goal.assume_rule_tac @{context} 1\<close>)
  done

lemma Uctor_rename: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow>
  \<forall>t pd p. (t, pd) \<in> set3_\<tau>_pre X \<union> set4_\<tau>_pre X \<longrightarrow> UFVars t (pd p) \<subseteq> FFVars_\<tau> t \<union> PFVars p \<union> AS \<Longrightarrow>
  imsupp u \<inter> (FFVars_\<tau> (\<tau>_ctor (map_\<tau>_pre id id fst fst X)) \<union> PFVars p \<union> AS) = {} \<Longrightarrow>
  u ` set2_\<tau>_pre X \<inter> set2_\<tau>_pre X = {} \<Longrightarrow>
  CCTOR X p = CCTOR (map_\<tau>_pre u u (\<lambda>(t, pu). (rrename_\<tau> u t, PUmap u t pu)) (\<lambda>(t, pu). (rrename_\<tau> u t, PUmap u t pu)) X) p"
  apply (rule sym[THEN trans[rotated]])
  apply (rule trans)
    apply (rule arg_cong2[OF refl, of _ _ CCTOR])
    apply (rule Pmap_imsupp_empty[symmetric])
      apply assumption
     apply assumption
    apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
    apply (erule conjE)+
    apply assumption
  unfolding PUmap_def
   apply (rule ff0.Umap_Uctor[symmetric])
    apply assumption
   apply assumption
  apply (rule ff0.Umap_cong_ids[symmetric])
    apply assumption
   apply assumption
  apply (rotate_tac -1)
  apply (drule set_rev_mp)
   apply (rule ff0.UFVars_subsets)
    apply (drule imsupp_image_subset)
    apply (rule Int_subset_empty1[rotated])
     apply assumption
    apply (rule Int_subset_empty2)
     apply assumption
    apply (rule subset_trans[rotated])
     apply (rule equalityD2[OF Un_assoc])
  apply (rule Un_upper2)
    apply (erule allE impE)+
     apply assumption
    apply assumption
   apply (drule imsupp_id_on)
  unfolding id_on_def
   apply (rotate_tac -1)
   apply (erule allE)
   apply (erule impE)
    apply assumption
  apply assumption
  done

lemma in_UNIV_simp: "A \<and> x \<in> UNIV \<longleftrightarrow> A" by auto
lemma prod_case_lam_simp: "(\<lambda>y x. (case x of (a, b) \<Rightarrow> f a b) = (case y of (a, b) \<Rightarrow> g a b))
  = (\<lambda>(a1, b1) (a2, b2). f a2 b2 = g a1 b1)" by auto

lemma Uctor_cong: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> bij (u'::'a \<Rightarrow> 'a) \<Longrightarrow> |supp u'| <o |UNIV::'a set| \<Longrightarrow>
  \<forall>t pd p. (t, pd) \<in> set3_\<tau>_pre x \<union> set4_\<tau>_pre x \<longrightarrow> UFVars t (pd p) \<subseteq> FFVars_\<tau> t \<union> PFVars p \<union> AS \<Longrightarrow>
  \<forall>t pd p. (t, pd) \<in> set3_\<tau>_pre x' \<union> set4_\<tau>_pre x' \<longrightarrow> UFVars t (pd p) \<subseteq> FFVars_\<tau> t \<union> PFVars p \<union> AS \<Longrightarrow>
  imsupp u \<inter> (FFVars_\<tau> (\<tau>_ctor (map_\<tau>_pre id id fst fst x)) \<union> PFVars p \<union> AS) = {} \<Longrightarrow> u ` set2_\<tau>_pre x \<inter> set2_\<tau>_pre x = {} \<Longrightarrow>
  imsupp u' \<inter> (FFVars_\<tau> (\<tau>_ctor (map_\<tau>_pre id id fst fst x')) \<union> PFVars p \<union> AS) = {} \<Longrightarrow> u' ` set2_\<tau>_pre x' \<inter> set2_\<tau>_pre x' = {} \<Longrightarrow>
  mr_rel_\<tau>_pre (inv u' \<circ> u) (inv u' \<circ> u) (\<lambda>(t, pd) (t', pd'). rrename_\<tau> u t = rrename_\<tau> u' t' \<and> PUmap u t pd = PUmap u' t' pd') (\<lambda>(t, pd) (t', pd'). rrename_\<tau> u t = rrename_\<tau> u' t' \<and> PUmap u t pd = PUmap u' t' pd') x x' \<Longrightarrow>
  CCTOR x p = CCTOR x' p"
apply (rule trans)
   apply (rule Uctor_rename)
       apply assumption+
  apply (rule sym[THEN trans[rotated]])
   apply (rule Uctor_rename)
       apply (rotate_tac 2)
       apply assumption+
  apply (rule arg_cong2[OF _ refl, of _ _ CCTOR])
  apply (rule iffD2[OF fun_cong[OF fun_cong[OF \<tau>_pre.mr_rel_eq[symmetric]]]])
  apply (rule iffD2[OF \<tau>_pre.mr_rel_map(1)])
        apply (assumption | rule supp_id_bound bij_id)+
  unfolding id_o OO_eq
  apply (rule iffD2[OF \<tau>_pre.mr_rel_map(3)])
         apply assumption+
  unfolding relcompp_conversep_Grp
  unfolding Grp_def in_UNIV_simp prod_case_lam_simp prod.inject
  apply (rule \<tau>_pre.mr_rel_mono_strong)
       apply (assumption | rule supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv)+
  apply (raw_tactic \<open>let val ctxt = @{context} in EVERY1 [
    REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
    Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let val [thm1, thm2] = map ((fn ct => infer_instantiate' context [SOME ct] @{thm prod.exhaust}) o snd) params
      in rtac context thm1 1 THEN rtac context thm2 1 end
    ) ctxt,
    hyp_subst_tac ctxt,
    K (unfold_thms_tac ctxt @{thms prod.case}),
    etac ctxt conjE,
    rtac ctxt conjI,
    rtac ctxt sym,
    assume_tac ctxt,
    rtac ctxt sym,
    assume_tac ctxt
  ] end\<close>)+
  done

lemma forall_imp_map_prod_id: "(\<forall>t pd p. (t, pd) \<in> map_prod f id ` A \<longrightarrow> g t pd p) = (\<forall>t pd p. (t, pd) \<in> A \<longrightarrow> g (f t) pd p)"
  by fastforce

lemma CTOR_cong: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> bij (u'::'a \<Rightarrow> 'a) \<Longrightarrow> |supp u'| <o |UNIV::'a set| \<Longrightarrow>
  \<forall>t pd p. (t, pd) \<in> set3_\<tau>_pre x \<union> set4_\<tau>_pre x \<longrightarrow> UFVars' t (pd p) \<subseteq> FVars_\<tau> t \<union> PFVars p \<union> AS \<Longrightarrow>
  \<forall>t pd p. (t, pd) \<in> set3_\<tau>_pre x' \<union> set4_\<tau>_pre x' \<longrightarrow> UFVars' t (pd p) \<subseteq> FVars_\<tau> t \<union> PFVars p \<union> AS \<Longrightarrow>
  imsupp u \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst x)) \<union> PFVars p \<union> AS) = {} \<Longrightarrow> u ` set2_\<tau>_pre x \<inter> set2_\<tau>_pre x = {} \<Longrightarrow>
  imsupp u' \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst x')) \<union> PFVars p \<union> AS) = {} \<Longrightarrow> u' ` set2_\<tau>_pre x' \<inter> set2_\<tau>_pre x' = {} \<Longrightarrow>
  mr_rel_\<tau>_pre (inv u' \<circ> u) (inv u' \<circ> u) (\<lambda>(t, pd) (t', pd'). alpha_\<tau> (rename_\<tau> u t) (rename_\<tau> u' t') \<and> PUmap' u t pd = PUmap' u' t' pd') (\<lambda>(t, pd) (t', pd'). alpha_\<tau> (rename_\<tau> u t) (rename_\<tau> u' t') \<and> PUmap' u t pd = PUmap' u' t' pd') x x' \<Longrightarrow>
  CTOR x p = CTOR x' p"
  unfolding CTOR_def
  apply (rule Uctor_cong)
            apply assumption
           apply assumption
          apply (rotate_tac 2)
          apply assumption+
  unfolding \<tau>_pre.set_map[OF id_prems] image_Un[symmetric] forall_imp_map_prod_id UFVars'_def[symmetric] FVars_\<tau>_def2[symmetric]
  apply assumption
       apply assumption
  apply (raw_tactic \<open>
    let
      val ctxt = @{context}
      val common_tac = EVERY' [
        REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
        rtac ctxt @{thm relcomppI},
        rtac ctxt refl,
        hyp_subst_tac ctxt,
        SELECT_GOAL (unfold_thms_tac @{context} @{thms comp_def}),
        rtac ctxt @{thm \<tau>.TT_Quotient_rep_abss}
      ];
    in EVERY1 [
      rtac ctxt trans,
      rtac ctxt @{thm arg_cong2[OF refl, of _ _ "(\<inter>)"]},
      REPEAT_DETERM o rtac ctxt @{thm arg_cong2[OF _ refl, of _ _ "(\<union>)"]},
      K (assume_tac ctxt 2),
      K (unfold_thms_tac ctxt @{thms FFVars_\<tau>_def \<tau>_ctor_def}),
      rtac ctxt @{thm \<tau>.alpha_FVarss},
      rtac ctxt @{thm \<tau>.alpha_transs},
      rtac ctxt @{thm \<tau>.TT_Quotient_rep_abss},
      rtac ctxt @{thm alpha_\<tau>.intros},
      rtac ctxt @{thm bij_id},
      rtac ctxt @{thm supp_id_bound},
      rtac ctxt @{thm id_on_id},
      K (unfold_thms_tac ctxt @{thms \<tau>_pre.map_comp[OF id_prems id_prems] o_id comp_assoc[symmetric] fst_comp_map_prod[symmetric] \<tau>.rename_ids}),
      rtac ctxt @{thm iffD2[OF \<tau>_pre.mr_rel_map(1)]},
      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
      K (unfold_thms_tac ctxt @{thms id_o}),
      rtac ctxt @{thm iffD2[OF \<tau>_pre.mr_rel_map(3)]},
      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
      K (unfold_thms_tac ctxt @{thms inv_o_simp1[OF bij_id] relcompp_conversep_Grp}),
      K (unfold_thms_tac ctxt @{thms Grp_UNIV_def}),
      rtac ctxt @{thm \<tau>_pre.mr_rel_mono_strong},
      REPEAT_DETERM o resolve_tac ctxt @{thms supp_id_bound bij_id},
      rtac ctxt @{thm iffD2[OF fun_cong[OF fun_cong[OF \<tau>_pre.mr_rel_eq]]]},
      rtac ctxt refl,
      REPEAT_DETERM o common_tac,
      K (unfold_thms_tac ctxt @{thms image_id}),
      assume_tac ctxt
    ] end\<close>)+
  apply (rule iffD2[OF \<tau>_pre.mr_rel_map(1)])
        apply (assumption | rule supp_id_bound bij_id supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv)+
  apply (rule iffD2[OF \<tau>_pre.mr_rel_map(3)])
         apply (assumption | rule supp_id_bound bij_id supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv)+
  unfolding relcompp_conversep_Grp inv_id id_o o_id
  unfolding Grp_UNIV_def
  apply (rule \<tau>_pre.mr_rel_mono_strong)
       apply (assumption | rule supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp bij_imp_bij_inv)+
  apply (raw_tactic \<open>let val ctxt = @{context} in EVERY1 [
    REPEAT_DETERM o resolve_tac ctxt [ballI, impI],
    Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let val [thm1, thm2] = map ((fn ct => infer_instantiate' context [SOME ct] @{thm prod.exhaust}) o snd) params
      in rtac context thm1 1 THEN rtac context thm2 1 end
    ) ctxt,
    hyp_subst_tac ctxt,
    K (unfold_thms_tac ctxt @{thms prod.case}),
    rtac ctxt @{thm relcomppI},
    resolve_tac ctxt @{thms fun_cong[OF map_prod_def] prod.case},
    K (unfold_thms_tac ctxt @{thms prod.case map_prod_def}),
    etac ctxt conjE,
    rtac ctxt conjI,
    K (unfold_thms_tac ctxt @{thms rrename_\<tau>_def}),
    rtac ctxt @{thm iffD2[OF \<tau>.TT_Quotient_total_abs_eq_iffs]},
    rtac ctxt @{thm \<tau>.alpha_transs},
    rtac ctxt @{thm iffD2[OF \<tau>.alpha_bij_eqs]},
    REPEAT_DETERM o assume_tac ctxt,
    rtac ctxt @{thm \<tau>.TT_Quotient_rep_abss},
    rtac ctxt @{thm \<tau>.alpha_transs[rotated]},
    rtac ctxt @{thm \<tau>.alpha_syms},
    rtac ctxt @{thm iffD2[OF \<tau>.alpha_bij_eqs]},
    REPEAT_DETERM o assume_tac ctxt,
    rtac ctxt @{thm \<tau>.TT_Quotient_rep_abss},
    assume_tac ctxt,
    SELECT_GOAL (unfold_thms_tac @{context} @{thms PUmap_def PUmap'_def id_def Umap'_def}),
    assume_tac ctxt
  ] end\<close>)+
  done

lemmas [fundef_cong] = \<tau>_pre.map_cong[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound _ refl refl]

function f0 :: "'a::var_\<tau>_pre raw_\<tau> \<Rightarrow> 'a ssfun \<Rightarrow> 'a U" where
  "f0 (raw_\<tau>_ctor x) p = CTOR (map_\<tau>_pre id id (\<lambda>t. (t, f0 t)) (\<lambda>t. (t, f0 t)) (map_\<tau>_pre id (pick0 x p) (rename_\<tau> (pick0 x p)) id x)) p"
  apply pat_completeness
  apply (erule Pair_inject)
  apply (drule iffD1[OF raw_\<tau>.inject])
  apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule refl)
  done
termination
  apply (relation "inv_image {(s, t). subshape_\<tau>_\<tau> s t} fst")
    apply (rule wf_inv_image)
    apply (rule \<tau>.wf_subshapes)
  unfolding in_inv_image prod_in_Collect_iff fst_conv \<tau>_pre.set_map[OF supp_id_bound pick0_prems] image_id
   apply (drule \<tau>.set_subshape_images[rotated -1])
     apply (rule pick0_prems)+
   apply assumption
  apply (drule \<tau>.set_subshapes)
  apply assumption
  done

lemma alpha_ctor_pick0: "alpha_\<tau> (raw_\<tau>_ctor x) (raw_\<tau>_ctor (
  map_\<tau>_pre id id fst fst (
    map_\<tau>_pre id (pick0 x p) (\<lambda>t. (rename_\<tau> (pick0 x p) t, f0 (rename_\<tau> (pick0 x p) t))) (\<lambda>t. (t, f0 t)) x
  )))"
  apply (rule alpha_\<tau>.intros[of "pick0 x p"])
     apply (rule pick0_prems)+
   apply (rule pick0_id_on)
  apply (rule iffD2[OF arg_cong2[OF refl, of "map_\<tau>_pre _ _ _ _ _" _ _ x]])
   apply (rule \<tau>_pre.map_comp)
        apply (rule supp_id_bound bij_id pick0_prems)+
  unfolding id_o
  unfolding comp_def fst_conv id_def[symmetric]
  apply (rule iffD2)
   apply (rule \<tau>_pre.mr_rel_map)
         apply (rule supp_id_bound bij_id pick0_prems)+
  unfolding relcompp_conversep_Grp inv_o_simp1[OF bij_id] inv_o_simp1[OF pick0_prems(1)]
  apply (rule \<tau>_pre.mr_rel_mono_strong0)
            apply (rule supp_id_bound bij_id)+
      apply (rule iffD1[OF fun_cong[OF fun_cong[OF \<tau>_pre.mr_rel_id]]])
      apply (rule iffD2[OF fun_cong[OF fun_cong[OF \<tau>_pre.rel_eq]]])
      apply (rule refl)
     apply (rule ballI, rule refl)+
   apply (rule ballI)+
   apply (rule impI)
   apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule \<tau>.alpha_refls)
  apply (rule ballI)+
  apply (rule impI)
  apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding id_apply
  apply (rule \<tau>.alpha_refls)
  done

lemma Umap'_alpha: "alpha_\<tau> t t' \<Longrightarrow> Umap' u t = Umap' u t'"
  unfolding Umap'_def
  apply (rule arg_cong2[OF refl, of _ _ Umap])
  apply (rule iffD2[OF \<tau>.TT_Quotient_total_abs_eq_iffs])
  apply assumption
  done

lemma PUmap'_alpha: "alpha_\<tau> t t' \<Longrightarrow> PUmap' u t = PUmap' u t'"
  unfolding PUmap'_def
  apply (rule arg_cong[of _ _ "\<lambda>f. (\<lambda>pu p. f (pu (mapP (inv u) p)))", OF Umap'_alpha])
  apply assumption
  done


lemma PFVars_mapP: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> PFVars (mapP u p) = u ` PFVars p"
  apply (rule iffD2[OF set_eq_iff])
  apply (rule allI)
  apply (rule sym[THEN trans[rotated]])
   apply (rule image_in_bij_eq)
  apply assumption
  apply (rule ff0.in_PFVars_Pmap)
   apply assumption+
  done

definition XXl :: "('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> 'a ssfun \<Rightarrow> ('a, 'a, 'a raw_\<tau>, 'a raw_\<tau>) \<tau>_pre \<Rightarrow> ('a, 'a, 'a raw_\<tau> \<times> ('a ssfun \<Rightarrow> 'a U), 'a raw_\<tau> \<times> ('a ssfun \<Rightarrow> 'a U)) \<tau>_pre" where
  "XXl u p x \<equiv> map_\<tau>_pre u (u \<circ> pick0 x (mapP (inv u) p))
    (\<lambda>xa. (rename_\<tau> (u \<circ> pick0 x (mapP (inv u) p)) xa, PUmap' u (rename_\<tau> (pick0 x (mapP (inv u) p)) xa) (f0 (rename_\<tau> (pick0 x (mapP (inv u) p)) xa))))
    (\<lambda>x. (rename_\<tau> u x, PUmap' u x (f0 x))) x"

definition XXr :: "('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> 'a ssfun \<Rightarrow> ('a, 'a, 'a raw_\<tau>, 'a raw_\<tau>) \<tau>_pre \<Rightarrow> ('a, 'a, 'a raw_\<tau> \<times> ('a ssfun \<Rightarrow> 'a U), 'a raw_\<tau> \<times> ('a ssfun \<Rightarrow> 'a U)) \<tau>_pre" where
  "XXr u p x \<equiv> map_\<tau>_pre u (pick0 (map_\<tau>_pre u u (rename_\<tau> u) (rename_\<tau> u) x) p \<circ> u)
            (\<lambda>xa. (rename_\<tau> (pick0 (map_\<tau>_pre u u (rename_\<tau> u) (rename_\<tau> u) x) p) (rename_\<tau> u xa), f0 (rename_\<tau> (pick0 (map_\<tau>_pre u u (rename_\<tau> u) (rename_\<tau> u) x) p) (rename_\<tau> u xa))))
            (\<lambda>x. (rename_\<tau> u x, f0 (rename_\<tau> u x))) x"

lemma int_empty_left: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> imsupp u \<inter> AS = {} \<Longrightarrow>
  set2_\<tau>_pre (XXl u p x) \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst (XXl u p x))) \<union> PFVars p \<union> AS) = {}"
  apply (rule trans)
   apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
   apply (rule arg_cong2[OF _ refl, of _ _ "(\<union>)"])+
   apply (rule arg_cong[of _ _ "\<lambda>x. FVars_\<tau> (raw_\<tau>_ctor x)"])
  unfolding XXl_def
   apply (rule \<tau>_pre.map_comp)
        apply (assumption | rule bij_comp supp_comp_bound pick0_prems infinite_var_\<tau>_pre supp_id_bound bij_id)+
  unfolding id_o o_id comp_def[of fst] fst_conv
  unfolding \<tau>.FVars_ctors
  apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
    let
      val bij_comp = @{thm bij_comp[OF pick0_prems(1)]} OF [hd prems];
      val supp_comp_bound = @{thm supp_comp_bound[OF pick0_prems(2)]} OF [nth prems 1, @{thm infinite_var_\<tau>_pre}]
      val thms' = map (fn thm => thm OF [nth prems 1, bij_comp, supp_comp_bound]) @{thms \<tau>_pre.set_map}
      val FVars_map = @{thm \<tau>.FVars_renames} OF [bij_comp, supp_comp_bound]
      val FVars_map' = @{thm \<tau>.FVars_renames} OF (take 2 prems)
      val diff_image = @{thm image_set_diff[OF bij_is_inj]} OF [bij_comp] RS sym
    in Ctr_Sugar_Tactics.unfold_thms_tac context (
      @{thms image_comp[unfolded comp_def] image_UN[symmetric]} @
      [FVars_map, FVars_map', diff_image] @ thms'
    ) end
  ) @{context} 1\<close>)
  unfolding image_comp[symmetric] id_on_image[OF pick0_id_on] image_Un[symmetric] \<tau>.FVars_ctors[symmetric]
  apply (rule bij_is_inj[THEN iffD1[OF inj_image_eq_iff]])
   apply (rule bij_imp_bij_inv)
   apply assumption
  apply (rule trans)
   apply (rule image_Int)
   apply (rule bij_is_inj)
   apply (rule bij_imp_bij_inv)
   apply assumption
  apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
    let
      val bij = hd prems
      val bij_inv = @{thm bij_imp_bij_inv} OF [bij]
      val supp_inv = @{thm supp_inv_bound} OF (take 2 prems)
    in Ctr_Sugar_Tactics.unfold_thms_tac context (
      @{thms id_o image_id image_comp image_empty o_assoc image_Un}
      @ [@{thm inv_o_simp1} OF [bij],
        @{thm PFVars_mapP[symmetric]} OF [bij_inv, supp_inv],
        @{thm id_on_image[OF id_on_inv[OF _ imsupp_id_on]]} OF [bij, nth prems 2]
      ]
    ) end
  ) @{context} 1\<close>)
  apply (insert suitable_pick0)
  unfolding suitable_def
  apply (erule allE[of _ x])
  apply (erule allE[of _ "mapP (inv u) p"])
  apply (erule conjE)+
  apply assumption
  done

lemma int_empty_right: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> imsupp u \<inter> AS = {} \<Longrightarrow>
  set2_\<tau>_pre (XXr u p x) \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst (XXr u p x))) \<union> PFVars p \<union> AS) = {}"
apply (rule trans)
   apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
   apply (rule arg_cong2[OF _ refl, of _ _ "(\<union>)"])+
   apply (rule arg_cong[of _ _ "\<lambda>x. FVars_\<tau> (raw_\<tau>_ctor x)"])
  unfolding XXr_def
   apply (rule \<tau>_pre.map_comp)
        apply (assumption | rule bij_comp supp_comp_bound pick0_prems infinite_var_\<tau>_pre supp_id_bound bij_id)+
  unfolding id_o o_id comp_def[of fst] fst_conv
  unfolding \<tau>.FVars_ctors
  apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
    let
      val bij_comp = @{thm bij_comp[OF _ pick0_prems(1)]} OF [hd prems];
      val supp_comp_bound = @{thm supp_comp_bound[OF _ pick0_prems(2)]} OF [nth prems 1, @{thm infinite_var_\<tau>_pre}]
      val thms' = map (fn thm => thm OF [nth prems 1, bij_comp, supp_comp_bound]) @{thms \<tau>_pre.set_map}
      val FVars_map = @{thm \<tau>.FVars_renames} OF [bij_comp, supp_comp_bound]
      val FVars_map' = @{thm \<tau>.FVars_renames} OF (take 2 prems)
      val FVars_map'2 = @{thm \<tau>.FVars_renames} OF @{thms pick0_prems}
      val diff_image = @{thm image_set_diff[OF bij_is_inj]} OF [bij_comp] RS sym
      val rename_comp' = @{thm \<tau>.rename_comps} OF (take 2 prems @ @{thms pick0_prems})
      val set_map_syms = map (fn thm => thm RS sym OF (nth prems 1 :: take 2 prems)) @{thms \<tau>_pre.set_map[of u u "rename_\<tau> u" "rename_\<tau> u" x]}
      val diff_image2 = @{thm image_set_diff[OF bij_is_inj]} OF [hd prems]
      val rename_simps = @{thm \<tau>.rename_simps} OF (take 2 prems)
    in unfold_thms_tac context (thms' @ [rename_comp']) THEN
      unfold_thms_tac context (
      @{thms image_comp[unfolded comp_def] image_UN[symmetric]} @ [FVars_map, FVars_map', diff_image]
    ) THEN unfold_thms_tac context (@{thms image_comp[symmetric] image_Un[symmetric] \<tau>.FVars_ctors[symmetric]} @ [
      @{thm id_on_image[OF pick0_id_on_image]} OF (take 2 prems), FVars_map' RS sym, rename_simps
    ]) THEN unfold_thms_tac context set_map_syms  end
  ) @{context} 1\<close>)
  apply (insert suitable_pick0)
  unfolding suitable_def
  apply (erule allE conjE)+
  apply assumption
  done

lemma fst_o_lam: "fst \<circ> (\<lambda>x. (f x, g x)) = f" by auto
lemma image_prod_f_g: "(a, b) \<in> (\<lambda>x. (f x, g (f x))) ` A \<longleftrightarrow> a \<in> f ` A \<and> b = g a" by blast
lemma Int_Un_empty: "A \<inter> (B \<union> C \<union> D) = {} \<longleftrightarrow> A \<inter> B = {} \<and> A \<inter> (C \<union> D) = {}" by blast

ML \<open>
val f0_t = @{term "f0 :: 'a::var_\<tau>_pre raw_\<tau> \<Rightarrow> _ \<Rightarrow> _"}
val P = @{typ "'a::var_\<tau>_pre ssfun"}
val U = @{typ "'a::var_\<tau>_pre U"}
val A = HOLogic.mk_prodT (raw_T, P --> U)

val map_id_fst_t = Term.list_comb (
  MRBNF_Def.mk_map_of_mrbnf [] [A, A] [raw_T, raw_T] vars vars tau, 
  MRBNF_Def.interlace [BNF_Util.fst_const A, BNF_Util.fst_const A] (map HOLogic.id_const vars) (map HOLogic.id_const vars) var_types
)
\<close>

lemma f0_UFVars': "UFVars' t (f0 t p) \<subseteq> FVars_\<tau> t \<union> PFVars p \<union> AS"
proof -
  have "\<And>t. \<forall>(p::'a::var_\<tau>_pre ssfun). UFVars' t (f0 t p) \<subseteq> FVars_\<tau> t \<union> PFVars p \<union> AS"
    apply (rule \<tau>.TT_subshape_induct)
    apply (rule allI)
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
    let val thm = infer_instantiate' context [SOME (snd (nth params 1))] @{thm raw_\<tau>.exhaust}
    in resolve_tac context [thm] 1 end
  ) @{context} 1 THEN hyp_subst_tac @{context} 1\<close>)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule arg_cong2[OF _ refl, of _ _ "(\<union>)"])+
     apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
    let
      val params' = map (Thm.term_of o snd) params
      val pick = @{term "pick0::_ \<Rightarrow> _ \<Rightarrow> 'a::var_\<tau>_pre \<Rightarrow> 'a"} $ nth params' 3 $ nth params' 2
      val bindRec = Term.abs ("t", raw_T) (HOLogic.mk_prod (
        rename_t $ pick $ Bound 0,
        f0_t $ (rename_t $ pick $ Bound 0)
      ));
      val otherRec = Term.abs ("t", raw_T) (HOLogic.pair_const raw_T (P --> U) $ Bound 0 $ (f0_t $ Bound 0));
      val t = @{term "raw_\<tau>_ctor::('a::var_\<tau>_pre, 'a, 'a raw_\<tau>, 'a raw_\<tau>) \<tau>_pre \<Rightarrow> 'a raw_\<tau>"} $ (
         map_id_fst_t $ (
            Term.list_comb (MRBNF_Def.mk_map_of_mrbnf [] [raw_T, raw_T] [A, A] vars vars tau,
              MRBNF_Def.interlace [bindRec, otherRec] [pick] (map HOLogic.id_const vars) var_types
            ) $ nth params' 3
        ));
      val thm = infer_instantiate' context [NONE, SOME (Thm.cterm_of context t)] @{thm \<tau>.alpha_FVarss}
    in resolve_tac context [thm] 1 end
  ) @{context} 1\<close>)
     apply (subst \<tau>_pre.map_comp[OF supp_id_bound pick0_prems id_prems])
    unfolding id_o fst_o_lam id_def[symmetric]
     apply (rule alpha_\<tau>.intros)
        apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
    let val thm = infer_instantiate' context [SOME (snd (nth params 3)), SOME (snd (nth params 2))] @{thm pick0_prems(1)}
    in resolve_tac context [thm] 1 end
  ) @{context} 1\<close>)
       apply (rule pick0_prems)
      apply (rule pick0_id_on)
     apply (rule iffD2[OF \<tau>_pre.mr_rel_map(3)])
            apply (rule id_prems pick0_prems)+
    unfolding inv_o_simp1[OF bij_id] Grp_UNIV_id conversep_eq OO_eq
     apply (rule \<tau>_pre.mr_rel_mono_strong0)
               apply (rule supp_id_bound bij_id bij_comp pick0_prems bij_imp_bij_inv supp_comp_bound supp_inv_bound)+
          apply (rule infinite_var_\<tau>_pre)
         defer
         apply (rule ballI, rule refl)
        apply (rule ballI, rule fun_cong[OF inv_o_simp1[symmetric]], rule pick0_prems)
       apply (rule ballI, rule ballI, rule impI, assumption)+
     defer
    unfolding mr_rel_\<tau>_pre_def \<tau>_pre.map_id relcompp_conversep_Grp f0.simps
     apply (rule \<tau>_pre.rel_refl_strong)
      apply (rule \<tau>.alpha_refls)
     apply (rule \<tau>.alpha_refls)
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
     apply (subst \<tau>_pre.map_comp[OF supp_id_bound pick0_prems id_prems])
    unfolding id_o o_id
    unfolding comp_def
     apply (rule refl)
    apply (rule UFVars'_CTOR)
    unfolding \<tau>_pre.set_map[OF supp_id_bound pick0_prems]
     apply (insert suitable_pick0)
    unfolding suitable_def Int_Un_empty
     apply (erule allE conjE)+
     apply assumption
    apply (erule UnE)
     apply (drule iffD1[OF image_prod_f_g])
     apply (erule conjE)
     apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (drule \<tau>.set_subshape_images[rotated -1])
       apply (rule pick0_prems)+
    unfolding atomize_all[symmetric]
     apply (raw_tactic \<open>Goal.assume_rule_tac @{context} 1\<close>)
    apply (drule iffD1[OF image_prod_f_g[of _ _ id, unfolded image_id, unfolded id_def]])
    apply (erule conjE)
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (drule \<tau>.set_subshapes)
    apply (raw_tactic \<open>Goal.assume_rule_tac @{context} 1\<close>)
    done
  then show ?thesis
    apply (rule allE)
    apply assumption
    done
qed


ML \<open>
fun rtac ctxt = resolve_tac ctxt o single
fun dtac ctxt = dresolve_tac ctxt o single
fun etac ctxt = eresolve_tac ctxt o single

val f0_t = @{term "f0 :: _ \<Rightarrow> 'a::var_\<tau>_pre ssfun \<Rightarrow> _"}
val Umap'_t = @{term "Umap' :: _ \<Rightarrow> _ \<Rightarrow> 'a::var_\<tau>_pre U \<Rightarrow> _"}
val CTOR_t = @{term "CTOR :: _ \<Rightarrow> _ \<Rightarrow> 'a::var_\<tau>_pre U"}
val mapP = @{term "mapP :: ('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> _ \<Rightarrow> _"}
val PFVars_t = @{term "PFVars :: 'a::var_\<tau>_pre ssfun \<Rightarrow> _"}
val avoiding_set = @{term "AS :: 'a::var_\<tau>_pre set"}
val XXl_t = @{term "XXl :: _ \<Rightarrow> 'a::var_\<tau>_pre ssfun \<Rightarrow> _"}
val XXr_t = @{term "XXr :: _ \<Rightarrow> 'a::var_\<tau>_pre ssfun \<Rightarrow> _"}
val FVars_t = @{term "FVars_\<tau> :: 'a::var_\<tau>_pre raw_\<tau> \<Rightarrow> _"}
val ctor_t = @{term "raw_\<tau>_ctor :: _ \<Rightarrow> 'a::var_\<tau>_pre raw_\<tau>"}


fun swapped thm a b = [thm OF [a, b], thm OF [b, a]]

val unfold_thms_tac = Ctr_Sugar_Tactics.unfold_thms_tac

fun topBindSet T = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 [])
  (replicate 4 [T, T])
  (replicate 4 [@{typ "'a::var_\<tau>_pre"}]) (replicate 4 [@{typ "'a::var_\<tau>_pre"}])
   tau) 1
\<close>

lemma image_prod_f_g': "(a, b) \<in> (\<lambda>x. (f x, g x)) ` A = (\<exists>x. x \<in> A \<and> a = f x \<and> b = g x)" by blast
lemma exists_middle: "x = f (g y) \<Longrightarrow> \<exists>z. z = g y \<and> f z = x" by blast
lemma inv_id_middle: "bij u \<Longrightarrow> inv f (g (u z)) = u z \<Longrightarrow> (inv u \<circ> (inv f \<circ> g \<circ> u)) z = id z" by simp
lemma inv_id_middle2: "bij R \<Longrightarrow> bij g \<Longrightarrow> (g \<circ> R) z2 = (f \<circ> L) z2 \<Longrightarrow> (inv R \<circ> (inv g \<circ> f \<circ> L)) z2 = id z2"
  by (metis bij_inv_eq_iff comp_apply id_apply)

lemma imsupp_id_on_XXl:
  assumes "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a)" "|supp u| <o |UNIV::'a set|"
  shows "imsupp f \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst (XXl u p x))) \<union> PFVars p \<union> AS) = {} \<Longrightarrow>
    id_on (u ` (\<Union> (FVars_\<tau> ` set3_\<tau>_pre x) - set2_\<tau>_pre x)) f \<and> id_on (u ` \<Union> (FVars_\<tau> ` set4_\<tau>_pre x)) f"
  apply (raw_tactic \<open>
    let
      val ctxt = @{context}
      val bij_comp = @{thm bij_comp[OF pick0_prems(1) assms(1)]}
      val supp_comp = @{thm supp_comp_bound[OF pick0_prems(2) assms(2) infinite_var_\<tau>_pre]}
      val comp_prems = [@{thm assms(2)}, bij_comp, supp_comp]
      val rename = @{thm \<tau>.FVars_renames} OF [bij_comp, supp_comp]
      val rename' = @{thm \<tau>.FVars_renames} OF @{thms assms}
      val set_diff = @{thm image_set_diff[OF bij_is_inj]} OF [bij_comp] RS sym
    in unfold_thms_tac ctxt (@{thms XXl_def id_o comp_def[of fst] fst_conv \<tau>.FVars_ctors image_comp
        comp_def[of FVars_\<tau>] image_UN[symmetric] Int_Un_distrib Un_empty}
      @ [@{thm \<tau>_pre.map_comp} OF (comp_prems @ @{thms id_prems}), rename, rename', set_diff]
      @ map (fn thm => thm OF comp_prems) @{thms \<tau>_pre.set_map}) end
    \<close>)
  apply (erule conjE)+
  apply (rotate_tac -1)
  apply (drule trans[rotated])
   apply (rule sym)
   apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
  unfolding image_comp[symmetric]
   apply (rule arg_cong2[OF refl, of _ _ "(`)"])
   apply (rule id_on_image[OF pick0_id_on])
  apply (rule conjI)
  apply (rule imsupp_id_on, assumption)+
  done
  
lemma imsupp_id_on_XXr:
  assumes "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a)" "|supp u| <o |UNIV::'a set|"
  shows "imsupp f \<inter> (FVars_\<tau> (raw_\<tau>_ctor (map_\<tau>_pre id id fst fst (XXr u p x))) \<union> PFVars p \<union> AS) = {} \<Longrightarrow>
    id_on (u ` (\<Union> (FVars_\<tau> ` set3_\<tau>_pre x) - set2_\<tau>_pre x)) f \<and> id_on (u ` \<Union> (FVars_\<tau> ` set4_\<tau>_pre x)) f"
  apply (raw_tactic \<open>
    let
      val ctxt = @{context}
      val bij_comp = @{thm bij_comp[OF assms(1) pick0_prems(1)]}
      val supp_comp = @{thm supp_comp_bound[OF assms(2) pick0_prems(2) infinite_var_\<tau>_pre]}
      val comp_prems = [@{thm assms(2)}, bij_comp, supp_comp]
      val rename = @{thm \<tau>.FVars_renames} OF [bij_comp, supp_comp]
      val rename' = @{thm \<tau>.FVars_renames} OF @{thms assms}
      val comp = @{thm \<tau>.rename_comps} OF @{thms assms pick0_prems}
      val set_diff = @{thm image_set_diff[OF bij_is_inj]} OF [bij_comp] RS sym
    in unfold_thms_tac ctxt (@{thms XXr_def id_o comp_def[of fst] fst_conv \<tau>.FVars_ctors image_comp
        comp_def[of FVars_\<tau>] image_UN[symmetric] Int_Un_distrib Un_empty}
      @ [@{thm \<tau>_pre.map_comp} OF (comp_prems @ @{thms id_prems}), rename, rename', set_diff, comp]
      @ map (fn thm => thm OF comp_prems) @{thms \<tau>_pre.set_map}) end
    \<close>)
  apply (erule conjE)+
  apply (rotate_tac -1)
  apply (drule trans[rotated])
   apply (rule sym)
   apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
  unfolding image_comp[symmetric]
   apply (rule id_on_image[OF pick0_id_on_image])
    apply (rule assms)+
  apply (rule conjI)
  apply (rule imsupp_id_on, assumption)+
  done

lemma f_swap_alpha: "bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> imsupp u \<inter> AS = {} \<Longrightarrow> alpha_\<tau> t t' \<Longrightarrow> f0 (rename_\<tau> u t) = PUmap' u t (f0 t) \<and> f0 t = f0 t'"
proof -
  have "\<And>t. \<forall>p t' u. bij (u::'a::var_\<tau>_pre \<Rightarrow> 'a) \<longrightarrow> |supp u| <o |UNIV::'a set| \<longrightarrow> imsupp u \<inter> AS = {} \<longrightarrow> alpha_\<tau> t t' \<longrightarrow>
  f0 (rename_\<tau> u t) p = PUmap' u t (f0 t) p \<and> f0 t = f0 t'"
    apply (rule \<tau>.TT_subshape_induct)
    apply (rule allI impI)+
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      resolve_tac context [infer_instantiate' context [SOME (snd (nth params 1))] @{thm raw_\<tau>.exhaust}] 1
    ) @{context} 1\<close>)
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule conjI)
    apply (rule trans)
     apply (rule arg_cong2[OF _ refl, of _ _ f0])
     apply (rule \<tau>.rename_simps)
      apply assumption
      apply assumption
    apply (rule trans[OF f0.simps])
    apply (rule sym)
    apply (rule trans)
     apply (rule fun_cong[OF fun_cong[OF PUmap'_alpha]])
     apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let
        val params' = map (Thm.term_of o snd) params
        val ct = Thm.cterm_of context (mapP $ MRBNF_Util.mk_inv (nth params' 4) $ nth params' 2)
      in rtac context (infer_instantiate' context [NONE, SOME ct] @{thm alpha_ctor_pick0}) 1 end
    ) @{context} 1\<close>)
    unfolding PUmap'_def
    apply (rule trans)
     apply (rule arg_cong3[OF refl refl, of _ _ Umap'])
     apply (rule trans[OF f0.simps])
     apply (rule arg_cong2[OF _ refl, of _ _ CTOR])
     apply (rule \<tau>_pre.map_comp)
          apply (rule pick0_prems supp_id_bound bij_id)+
    unfolding comp_def id_def
    unfolding id_def[symmetric]
    apply (rule trans)
     apply (rule Umap'_CTOR)
      apply assumption
     apply assumption
    apply (rule trans)
     apply (rule arg_cong2[OF refl, of _ _ CTOR])
     apply (rule trans)
      apply (rule fun_cong[OF ff0.Pmap_comp0, THEN sym, unfolded comp_def])
         apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
    unfolding fun_cong[OF ff0.Pmap_id0] inv_simp2 id_def[symmetric]
     apply (rule id_apply)
    apply (rule trans)
     apply (rule arg_cong2[OF _ refl, of _ _ CTOR])
     apply (rule \<tau>_pre.map_comp)
          apply (assumption | rule supp_id_bound bij_id pick0_prems)+
    apply (rule sym[THEN trans[rotated]])
     apply (rule arg_cong2[OF _ refl, of _ _ CTOR])
     apply (rule trans)
      apply (rule \<tau>_pre.map_comp)
           apply (assumption | rule supp_id_bound bij_id pick0_prems)+
    unfolding id_o o_id
     apply (rule \<tau>_pre.map_comp)
          apply (assumption | rule supp_id_bound bij_id pick0_prems)+
    unfolding id_o o_id comp_def[of "_ :: _ \<Rightarrow> _ * _"] prod.case
    apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      unfold_thms_tac context [@{thm \<tau>.rename_comps} OF (@{thms pick0_prems} @ take 2 (tl prems))]
    ) @{context} 1\<close>)
    unfolding XXl_def[symmetric] XXr_def[symmetric] triv_forall_equality
    apply (raw_tactic \<open>
      let
        val ctxt = @{context}
        val bound_tac = EVERY' [
          rtac ctxt @{thm \<tau>_pre.Un_bound},
          rtac ctxt @{thm set2_\<tau>_pre_bound},
          rtac ctxt @{thm \<tau>_pre.Un_bound},
          rtac ctxt @{thm \<tau>_pre.Un_bound},
          rtac ctxt @{thm \<tau>.card_of_FVars_bounds},
          rtac ctxt @{thm ff0.small_PFVars},
          rtac ctxt @{thm ff0.small_avoiding_sets}
        ]
        val set_map_tac = Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
          let
            val [_, bij, supp] = take 3 prems
            val comp_bijs = swapped @{thm bij_comp} bij @{thm pick0_prems(1)}
            val supp_comps = swapped @{thm supp_comp_bound[OF _ _ infinite_var_\<tau>_pre]} supp @{thm pick0_prems(2)}
            val set_maps = maps (fn thm => map2 (fn a => fn b => thm OF [supp, a, b]) comp_bijs supp_comps) @{thms \<tau>_pre.set_map}
          in unfold_thms_tac context (@{thms XXl_def XXr_def} @ set_maps) THEN rtac context refl 1 end
        ) ctxt
      in EVERY1 [
        Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
          let
            val [p, _, u, x] = map (Thm.term_of o snd) (take 4 params)
            val fA = Term.abs ("x", fastype_of x) (Term.list_comb (XXl_t, [u, p, Bound 0]))
            val AxT = snd (dest_funT (fastype_of fA))
            val f = Thm.cterm_of context (Term.abs ("Ax", AxT) (topBindSet A $ Bound 0))
            val g = Thm.cterm_of context (Term.abs ("Ax", AxT) (
              MRBNF_Util.mk_Un (MRBNF_Util.mk_Un (
                FVars_t $ (ctor_t $ (map_id_fst_t $ Bound 0)),
                PFVars_t $ p),
                avoiding_set)
            ));
            val thm = infer_instantiate' context [
              NONE, NONE, SOME f, SOME (Thm.cterm_of context fA), SOME (snd (nth params 3)),
              SOME g
            ] @{thm exists_bij_betw[OF infinite_var_\<tau>_pre]}
          in rtac context (exE OF [Drule.rotate_prems 2 thm]) 1 end
        ) ctxt,
        bound_tac,
        rtac ctxt @{thm int_empty_left},
        REPEAT_DETERM o assume_tac ctxt,
        set_map_tac,
        bound_tac,
        rtac ctxt @{thm int_empty_right},
        REPEAT_DETERM o assume_tac ctxt,
        set_map_tac,
        REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms bij_comp pick0_prems}),
        REPEAT_DETERM o eresolve_tac ctxt [exE, conjE]
      ] end\<close>)
    apply (rule CTOR_cong)
              apply (rotate_tac -9)
              apply assumption
             apply assumption
            apply (rotate_tac -5)
            apply assumption
            apply assumption
    apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      let
        val [IH, bij, supp, imsupp] = take 4 prems
        val bij_comp = @{thm bij_comp} OF [@{thm pick0_prems(1)}, bij]
        val supp_comp = @{thm supp_comp_bound} OF [@{thm pick0_prems(2)}, supp, @{thm infinite_var_\<tau>_pre}]
        fun common_tac ctxt = EVERY' [
          dtac ctxt IH,
          K (unfold_thms_tac ctxt @{thms PUmap'_def}),
          REPEAT_DETERM o etac ctxt allE,
          REPEAT_DETERM o (etac ctxt impE THEN' resolve_tac ctxt prems),
          etac ctxt impE,
          rtac ctxt @{thm \<tau>.alpha_refls},
          etac ctxt conjE,
          dtac ctxt sym,
          rotate_tac ~1,
          rtac ctxt @{thm iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]]},
          rtac ctxt @{thm arg_cong2[OF refl, of _ _ UFVars']},
          assume_tac ctxt,
          rtac ctxt @{thm subset_trans[rotated]},
          rtac ctxt @{thm f0_UFVars'},
          rtac ctxt @{thm subset_refl}
        ];
        fun subset_subshape_tac XX_def ctxt = EVERY1 [
          REPEAT_DETERM o resolve_tac ctxt [allI, impI],
          K (unfold_thms_tac ctxt (XX_def :: map (fn thm => thm OF [supp, bij_comp, supp_comp]) @{thms \<tau>_pre.set_map})),
          etac ctxt @{thm UnE},
          (* binding set *)
          K (unfold_thms_tac ctxt @{thms image_prod_f_g'}),
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          dtac ctxt trans,
          rtac ctxt @{thm \<tau>.rename_comps[symmetric]},
          REPEAT_DETERM o resolve_tac ctxt (@{thms pick0_prems} @ prems),
          rotate_tac ~1,
          dtac ctxt @{thm exists_middle[of _ "rename_\<tau> _"]},
          etac ctxt exE,
          etac ctxt conjE,
          rotate_tac ~2,
          dtac ctxt @{thm image_eqI[rotated]},
          assume_tac ctxt,
          dtac ctxt @{thm \<tau>.set_subshape_images(1)[rotated -1]},
          REPEAT_DETERM o resolve_tac ctxt @{thms pick0_prems},
          hyp_subst_tac ctxt,
          common_tac ctxt,
          (* nonbinding set *)
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          hyp_subst_tac ctxt,
          dtac ctxt @{thm \<tau>.set_subshapes(2)},
          common_tac ctxt
        ]
      in subset_subshape_tac @{thm XXl_def} context end
    ) @{context} 1\<close>)
        apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      let
        val [_, bij, supp, imsupp] = take 4 prems
        val bij_comp = @{thm bij_comp} OF [bij, @{thm pick0_prems(1)}]
        val supp_comp = @{thm supp_comp_bound} OF [supp, @{thm pick0_prems(2)}, @{thm infinite_var_\<tau>_pre}]
        fun common_tac ctxt = EVERY' [
          rtac ctxt @{thm subset_trans[rotated]},
          rtac ctxt @{thm f0_UFVars'},
          rtac ctxt @{thm subset_refl}
        ];
        fun subset_subshape_tac XX_def ctxt = EVERY1 [
          REPEAT_DETERM o resolve_tac ctxt [allI, impI],
          K (unfold_thms_tac ctxt (XX_def :: map (fn thm => thm OF [supp, bij_comp, supp_comp]) @{thms \<tau>_pre.set_map})),
          etac ctxt @{thm UnE},
          (* binding set *)
          K (unfold_thms_tac ctxt @{thms image_prod_f_g'}),
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          REPEAT_DETERM o resolve_tac ctxt (@{thms pick0_prems} @ prems),
          rotate_tac ~1,
          dtac ctxt @{thm exists_middle[of _ "rename_\<tau> _"]},
          etac ctxt exE,
          etac ctxt conjE,
          rotate_tac ~2,
          dtac ctxt @{thm image_eqI[rotated]},
          assume_tac ctxt,
          dtac ctxt @{thm \<tau>.set_subshape_images(1)[rotated -1]},
          REPEAT_DETERM o resolve_tac ctxt prems,
          hyp_subst_tac ctxt,
          common_tac ctxt,
          (* nonbinding set *)
          REPEAT_DETERM o eresolve_tac ctxt [exE, conjE],
          hyp_subst_tac ctxt,
          dtac ctxt @{thm \<tau>.set_subshapes(2)},
          common_tac ctxt
        ]
      in subset_subshape_tac @{thm XXr_def} context end
    ) @{context} 1\<close>)
          apply assumption
         apply assumption
        apply assumption
      apply assumption
(* mr_rel *)
    apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, ...} =>
      unfold_thms_tac context @{thms XXl_def XXr_def}
    ) @{context} 1\<close>) (* only unfold in goal *)
     apply (rule iffD2[OF \<tau>_pre.mr_rel_map(1)])
           apply (assumption | rule bij_comp pick0_prems supp_comp_bound infinite_var_\<tau>_pre supp_inv_bound bij_imp_bij_inv)+
     apply (rule iffD2[OF \<tau>_pre.mr_rel_map(3)])
            apply (assumption | rule supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre bij_comp pick0_prems bij_imp_bij_inv)+
    unfolding relcompp_conversep_Grp mr_rel_\<tau>_pre_def
     apply (rule iffD2[OF \<tau>_pre.rel_cong])
         apply (rule \<tau>_pre.map_cong0)
                  apply (rule supp_id_bound bij_id bij_comp pick0_prems bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_var_\<tau>_pre | assumption)+

    apply (raw_tactic \<open>
      let
        val ctxt = @{context}
        fun solve_tac n1 n2 inv = EVERY' [
          rotate_tac n1,
          dtac ctxt @{thm imsupp_id_on},
          rotate_tac ~1,
          dtac ctxt @{thm id_on_antimono},
          REPEAT_DETERM o (rtac ctxt @{thm subset_trans[rotated]} THEN' rtac ctxt @{thm Un_upper1}),
          rotate_tac n2,
          Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
            let
              val [bij, supp] = take 2 prems
              val [bij_comp, supp_comp] = [
                @{thm bij_comp} OF [@{thm pick0_prems(1)}, bij],
                @{thm supp_comp_bound} OF [@{thm pick0_prems(2)}, supp, @{thm infinite_var_\<tau>_pre}]
              ];
              val [bij_comp2, supp_comp2] = [
                @{thm bij_comp} OF [bij, @{thm pick0_prems(1)}],
                @{thm supp_comp_bound} OF [supp, @{thm pick0_prems(2)}, @{thm infinite_var_\<tau>_pre}]
              ];
              val thms = maps (fn prems => (
                @{thm \<tau>_pre.map_comp} OF (prems @ @{thms id_prems})) ::
                map (fn thm => thm OF prems) @{thms \<tau>_pre.set_map}
              ) [[supp, bij_comp, supp_comp], [supp, bij_comp2, supp_comp2]];
            in unfold_thms_tac context (@{thms id_o} @ thms) end
          ) ctxt,
          rtac ctxt @{thm subset_refl},
          (if inv then dtac ctxt @{thm id_on_inv[rotated]} THEN' assume_tac ctxt else K all_tac),
          K (unfold_thms_tac ctxt @{thms id_on_def image_iff}),
          etac ctxt allE,
          etac ctxt impE,
          rtac ctxt bexI,
          K (assume_tac ctxt 2),
          rtac ctxt refl,
          assume_tac ctxt
        ];
      in EVERY1 [
        SELECT_GOAL (unfold_thms_tac ctxt @{thms \<tau>.FVars_ctors XXl_def XXr_def}),
        rtac ctxt @{thm inv_id_middle},
        assume_tac ctxt,
        rtac ctxt trans,
        rtac ctxt @{thm arg_cong[of _ _ "inv _"]},
        solve_tac ~10 ~4 false,
        solve_tac ~4 ~10 true
      ] end\<close>)

           apply (rule inv_id_middle2)
             apply (assumption | rule bij_comp pick0_prems)+
           apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms eq_on_def}) 1\<close>)
           apply (erule allE)
           apply (erule impE)
            apply assumption
           apply (rule sym)
           apply assumption

          apply (rule refl)+
    unfolding \<tau>_pre.map_id
     apply (rule \<tau>_pre.rel_refl_strong)

      apply (rule relcomppI)
    unfolding Grp_UNIV_def
       apply (rule refl)
    unfolding prod.case
    apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      let
        val [_, bij, supp, _, _, f_bij, f_supp, _, _, g_bij, g_supp] = take 11 prems
        val rename_comp = @{thm \<tau>.rename_comps} OF ([bij, supp] @ @{thms pick0_prems})
        val bij_comps = swapped @{thm bij_comp} bij @{thm pick0_prems(1)}
        val supp_comps = swapped @{thm supp_comp_bound[OF _ _ infinite_var_\<tau>_pre]} supp @{thm pick0_prems(2)}

        val rename_comps = @{map 4} (fn bij_comp => fn supp_comp => fn b => fn s =>
          @{thm \<tau>.rename_comps} OF [bij_comp, supp_comp, b, s]
        ) (swapped @{thm bij_comp} bij @{thm pick0_prems(1)})
          (swapped @{thm supp_comp_bound[OF _ _ infinite_var_\<tau>_pre]} supp @{thm pick0_prems(2)})
          [g_bij, f_bij]
          [g_supp, f_supp];
      in unfold_thms_tac context [rename_comp] THEN unfold_thms_tac context rename_comps end
    ) @{context} 1\<close>)
      apply (rule conjI)
       apply (rule \<tau>.alpha_bijs)
            apply (assumption | rule bij_comp pick0_prems supp_comp_bound infinite_var_\<tau>_pre)+
        apply (rule ballI)
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let
        val [_, _ , _, x, _, _, _, z] = map (Thm.term_of o snd) params
        val set = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 []) (replicate 4 [raw_T, raw_T]) (replicate 4 vars) (replicate 4 vars) tau) 1
        val ct = Thm.cterm_of context (HOLogic.mk_mem (
          z, set $ x
        ));
        val thm = Local_Defs.unfold0 context @{thms eq_True eq_False} (
          infer_instantiate' context [SOME ct] @{thm bool.exhaust}
        );
      in EVERY1 [
        rtac context thm,
        SELECT_GOAL (unfold_thms_tac context @{thms eq_on_def})
      ] end
    ) @{context} 1\<close>)
         apply (erule allE)
         apply (erule impE)
          apply assumption
         apply assumption
        apply (rotate_tac -3)
        apply (drule UN_I)
         apply assumption
        apply (rotate_tac -1)
        apply (drule DiffI)
         apply assumption
        apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
          let
            fun mk_arg_cong n = infer_instantiate' context [NONE, NONE, SOME (snd (nth params n))] arg_cong
            val trans2 = @{thm sym[THEN trans[rotated]]}
          in EVERY1 [
            K (unfold_thms_tac context @{thms comp_def}),
            rtac context trans,
            rtac context (mk_arg_cong 4),
            rtac context (mk_arg_cong 2),
            forward_tac context @{thms id_onD[OF pick0_id_on]},
            assume_tac context,
            rtac context trans2,
            rtac context (mk_arg_cong 5),
            rotate_tac ~1,
            forward_tac context [infer_instantiate' context [NONE, NONE, SOME (snd (nth params 2))] @{thm imageI}],
            dtac context @{thm id_onD[OF pick0_id_on_image, rotated -1]},
            assume_tac context,
            assume_tac context,
            assume_tac context
          ] end
        ) @{context} 1\<close>)
        apply (frule imsupp_id_on_XXl[rotated -1])
          apply assumption
         apply assumption
    apply (drule conjunct1)
        apply (drule id_onD)
         apply (rule imageI)
         apply assumption
        apply (rule trans)
         apply assumption
        apply (rule sym[THEN trans[rotated]])
         apply (frule imsupp_id_on_XXr[rotated -1])
           apply assumption
          apply assumption
         apply (drule conjunct1)
         apply (drule id_onD)
          apply (rule imageI)
          apply assumption
         apply assumption
        apply (rule refl)
    apply (rule \<tau>.alpha_refls)

    unfolding PUmap'_def
      apply (rule ext)
      apply (frule \<tau>.set_subshape_images(1)[OF _ _ imageI, rotated -1])
         apply (rule pick0_prems)+
    apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      rtac context (allE OF [hd prems OF [nth prems 15]]) 1
    ) @{context} 1\<close>)
      apply (erule allE)+
      apply (erule impE)
       apply assumption
      apply (erule impE)
       apply assumption
      apply (erule impE)
       apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
       apply (erule conjE)+
       apply assumption
      apply (erule impE)
    apply (rule \<tau>.alpha_refls)
       apply (drule conjunct1)
       apply (rule trans)
        apply (rotate_tac -2)
        apply (rule arg_cong[of _ _ "Umap' _ _"])
        apply (rule sym)
        apply assumption
       apply (frule \<tau>.set_subshape_images(1)[OF _ _ imageI, rotated -1])
         apply (rule bij_comp)
          apply (rule pick0_prems)
         apply assumption
        apply (rule supp_comp_bound)
          apply (rule pick0_prems)
         apply assumption
        apply (rule infinite_var_\<tau>_pre)
    apply (rotate_tac -1)
apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      rtac context (allE OF [nth prems 1 OF [hd prems]]) 1
    ) @{context} 1\<close>)
       apply (erule allE)+
       apply (erule impE)
        apply (rotate_tac 6)
        apply assumption
       apply (erule impE)
        apply assumption
    apply (erule impE)
        apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
        apply (erule conjE)+
        apply assumption
       apply (erule impE)
    apply (rule \<tau>.alpha_refls)
    apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      let
        val [_, _, bij, supp] = take 4 prems
        val rename_comp = @{thm \<tau>.rename_comps} OF (@{thms pick0_prems} @ [bij, supp])
      in unfold_thms_tac context [rename_comp] end
  ) @{context} 1\<close>)
        apply (drule conjunct1)
        apply (rule trans)
         apply (rule sym)
         apply (rotate_tac -2)
         apply assumption
        apply (rule trans[rotated])
         apply (frule \<tau>.set_subshape_images(1)[OF _ _ imageI, rotated -1])
           apply (rule bij_comp)
            apply assumption
           apply (rule pick0_prems)
          apply (rule supp_comp_bound)
            apply assumption
           apply (rule pick0_prems)
          apply (rule infinite_var_\<tau>_pre)
    apply (rotate_tac -1)
    apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      rtac context (allE OF [nth prems 2 OF [hd prems]]) 1
    ) @{context} 1\<close>)
         apply (erule allE)+
         apply (erule impE)
          apply (rotate_tac 11)
          apply assumption
         apply (erule impE)
          apply assumption
    apply (erule impE)
    apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
          apply (erule conjE)+
          apply assumption
         apply (erule impE)
    apply (rule \<tau>.alpha_refls)
          apply (drule conjunct1)
          apply (rotate_tac -2)
          apply assumption
      apply (rule fun_cong[of "f0 _"])
      apply (rotate_tac 2)
    apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      let
        val [bij, supp, _, _, f_bij, f_supp, _, _, g_bij, g_supp] = take 10 prems
        val bij_comps = swapped @{thm bij_comp} bij @{thm pick0_prems(1)}
        val supp_comps = swapped @{thm supp_comp_bound[OF _ _ infinite_var_\<tau>_pre]} supp @{thm pick0_prems(2)}
        val rename_comps = @{map 4} (fn a => fn b => fn c => fn d => @{thm \<tau>.rename_comps} OF [a, b, c, d])
          bij_comps supp_comps [g_bij, f_bij] [g_supp, f_supp]
      in unfold_thms_tac context rename_comps end
    ) @{context} 1\<close>)
      apply (frule \<tau>.set_subshape_images(1)[OF _ _ imageI, rotated -1])
        apply (rule bij_comp)
         apply (rule bij_comp)
          apply (rule pick0_prems)
         apply assumption
        apply (rotate_tac 4)
        apply assumption
       apply (assumption | rule supp_comp_bound pick0_prems infinite_var_\<tau>_pre)+
      apply (rotate_tac -2)
 apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      rtac context (allE OF [hd prems OF [nth prems 1]]) 1
    ) @{context} 1\<close>)
      apply (erule allE)+
      apply (erule impE, assumption)+
      apply (erule impE)
       defer
       apply (drule conjunct2)
       apply assumption


      apply (rule relcomppI)
       apply (rule refl)
    unfolding prod.case
      apply (rule conjI)
       apply (rule \<tau>.alpha_bijs)
            apply assumption+
    unfolding \<tau>.FVars_renames
        apply (rule ballI)
        apply (rotate_tac -2)
        apply (frule UN_I)
         apply (rotate_tac 1)
         apply assumption
    unfolding image_UN[symmetric]
        apply (frule imsupp_id_on_XXl[rotated -1])
          apply assumption
         apply assumption
        apply (drule conjunct2)
        apply (drule id_onD)
         apply assumption
        apply (rule trans)
         apply assumption
        apply (frule imsupp_id_on_XXr[rotated -1])
          apply assumption
         apply assumption
        apply (drule conjunct2)
        apply (drule id_onD)
         apply assumption
        apply (rule sym)
        apply assumption
       apply (rule \<tau>.alpha_refls)
      apply (rule ext)
      apply (rule trans)
       apply (rule arg_cong[of _ _ "Umap' _ _"])
       apply (frule \<tau>.set_subshapes(2))
       apply (rotate_tac -1)
apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      rtac context (allE OF [nth prems 1 OF [hd prems]]) 1
    ) @{context} 1\<close>)
       apply (erule allE)+
       apply (erule impE, assumption)+
       apply (erule impE)
        apply (rule \<tau>.alpha_refls)
       apply (drule conjunct1)
       apply (rule sym)
       apply assumption
      apply (rule trans)
       apply (frule \<tau>.set_subshape_images(2)[OF _ _ imageI, rotated -1])
         apply assumption
        apply assumption
       apply (rotate_tac -1)
apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      rtac context (allE OF [nth prems 1 OF [hd prems]]) 1
    ) @{context} 1\<close>)
       apply (erule allE)+
    apply (rotate_tac 6)
       apply (erule impE, assumption)+
    apply (erule impE)
apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
          apply (erule conjE)+
        apply assumption
       apply (erule impE)
        apply (rule \<tau>.alpha_refls)
       apply (drule conjunct1)
       apply (rule sym)
       apply assumption
      apply (rule trans[rotated])
apply (frule \<tau>.set_subshape_images(2)[OF _ _ imageI, rotated -1])
         apply assumption
    apply assumption
    apply (rotate_tac -1)
apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      rtac context (allE OF [nth prems 1 OF [hd prems]]) 1
    ) @{context} 1\<close>)
apply (erule allE)+
       apply (rotate_tac 10)
apply (erule impE, assumption)+
    apply (erule impE)
apply (raw_tactic \<open>SELECT_GOAL (unfold_thms_tac @{context} @{thms Int_Un_distrib Un_empty}) 1\<close>)
          apply (erule conjE)+
        apply assumption
       apply (erule impE)
        apply (rule \<tau>.alpha_refls)
       apply (drule conjunct1)
       apply assumption
    unfolding \<tau>.rename_comps
      apply (frule \<tau>.set_subshape_images(2)[OF _ _ imageI, rotated -1])
        apply (rule bij_comp)
         apply assumption
        apply (rotate_tac 5)
        apply assumption
       apply (assumption | rule supp_comp_bound infinite_var_\<tau>_pre)+
apply (rotate_tac -1)
apply (raw_tactic \<open>Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
      rtac context (allE OF [nth prems 1 OF [hd prems]]) 1
    ) @{context} 1\<close>)
      apply (erule allE)+
      apply (erule impE, assumption)+
      apply (erule impE)
       defer
       apply (drule conjunct2)
       apply (rule fun_cong[of "f0 _"])
       apply assumption
      defer

      (* copied from earlier, slight adjustments *)
      apply (rule \<tau>.alpha_bijs)
           apply (assumption | rule bij_comp pick0_prems supp_comp_bound infinite_var_\<tau>_pre)+
apply (rule ballI)
    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      let
        val [_, _ , _, x, _, _, _, _, z] = map (Thm.term_of o snd) params
        val set = nth (MRBNF_Def.mk_sets_of_mrbnf (replicate 4 []) (replicate 4 [raw_T, raw_T]) (replicate 4 vars) (replicate 4 vars) tau) 1
        val ct = Thm.cterm_of context (HOLogic.mk_mem (
          z, set $ x
        ));
        val thm = Local_Defs.unfold0 context @{thms eq_True eq_False} (
          infer_instantiate' context [SOME ct] @{thm bool.exhaust}
        );
      in EVERY1 [
        rtac context thm,
        SELECT_GOAL (unfold_thms_tac context @{thms eq_on_def})
      ] end
    ) @{context} 1\<close>)
         apply (erule allE)
         apply (erule impE)
         apply assumption
        apply assumption
apply (rotate_tac -7)
        apply (drule UN_I)
         apply assumption
        apply (rotate_tac -1)
        apply (drule DiffI)
         apply assumption
        apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
          let
            fun mk_arg_cong n = infer_instantiate' context [NONE, NONE, SOME (snd (nth params n))] arg_cong
            val trans2 = @{thm sym[THEN trans[rotated]]}
          in EVERY1 [
            K (unfold_thms_tac context @{thms comp_def}),
            rtac context trans,
            rtac context (mk_arg_cong 4),
            rtac context (mk_arg_cong 2),
            forward_tac context @{thms id_onD[OF pick0_id_on]},
            assume_tac context,
            rtac context trans2,
            rtac context (mk_arg_cong 5),
            rotate_tac ~1,
            forward_tac context [infer_instantiate' context [NONE, NONE, SOME (snd (nth params 2))] @{thm imageI}],
            dtac context @{thm id_onD[OF pick0_id_on_image, rotated -1]},
            assume_tac context,
            assume_tac context,
            assume_tac context
          ] end
        ) @{context} 1\<close>)
        apply (frule imsupp_id_on_XXl[rotated -1])
          apply assumption
         apply assumption
    apply (drule conjunct1)
        apply (drule id_onD)
         apply (rule imageI)
         apply assumption
        apply (rule trans)
         apply assumption
        apply (rule sym[THEN trans[rotated]])
         apply (frule imsupp_id_on_XXr[rotated -1])
           apply assumption
          apply assumption
         apply (drule conjunct1)
         apply (drule id_onD)
          apply (rule imageI)
          apply assumption
        apply assumption
       apply (rule refl)
      apply (rule \<tau>.alpha_refls)

    unfolding \<tau>.rename_comps[symmetric]
     apply (rule \<tau>.alpha_bijs)
          apply assumption+
    unfolding \<tau>.FVars_renames
      apply (rule ballI)
      apply (rotate_tac -2)
      apply (frule UN_I)
       apply (rotate_tac 1)
       apply assumption
    unfolding image_UN[symmetric]
      apply (frule imsupp_id_on_XXl[rotated -1])
        apply assumption+
      apply (drule conjunct2)
      apply (drule id_onD)
       apply assumption
      apply (rule trans)
       apply assumption
      apply (frule imsupp_id_on_XXr[rotated -1])
        apply assumption+
      apply (drule conjunct2)
      apply (drule id_onD)
       apply assumption
      apply (rule sym)
      apply assumption
    apply (rule \<tau>.alpha_refls)

    apply (raw_tactic \<open>Subgoal.FOCUS_PARAMS (fn {context, params, ...} =>
      rtac context (infer_instantiate' context [SOME (snd (hd params))] @{thm raw_\<tau>.exhaust}) 1
    ) @{context} 1 THEN hyp_subst_tac @{context} 1\<close>)
    apply (rule ext)
    unfolding f0.simps \<tau>_pre.map_comp[OF supp_id_bound pick0_prems id_prems] id_o o_id
    unfolding comp_def


      thm f0_UFVars'

    oops

definition ff0 :: "'a::var_\<tau>_pre \<tau> \<Rightarrow> 'a ssfun \<Rightarrow> 'a U" where "ff0 t p \<equiv> f0 (quot_type.rep Rep_\<tau> t) p"

definition nnoclash :: "('a::var_\<tau>_pre, 'a, 'a \<tau>, 'a \<tau>) \<tau>_pre \<Rightarrow> bool" where
  "nnoclash x \<equiv> set2_\<tau>_pre x \<inter> (set1_\<tau>_pre x \<union> (\<Union>z\<in>set4_\<tau>_pre x. FFVars_\<tau> z)) = {}"


(* TODO: Prove with quotient *)
(*lemma rep_\<tau>_ctor: "quot_type.rep Rep_\<tau> (\<tau>_ctor x) = raw_\<tau>_ctor (map_\<tau>_pre id id (quot_type.rep Rep_\<tau>) (quot_type.rep Rep_\<tau>) x)"
  sorry




theorem ff0_cctor: "set2_\<tau>_pre x \<inter> (imsupp (Rep_ssfun p) \<union> {}) = {} \<Longrightarrow> nnoclash x \<Longrightarrow>
  ff0 (\<tau>_ctor x) p = CCTOR (map_\<tau>_pre id id (\<lambda>t. (t, ff0 t)) (\<lambda>t. (t, ff0 t)) x) p"
  unfolding ff0_def rep_\<tau>_ctor f.simps CTOR_def
  apply (rule arg_cong2[OF _ refl, of _ _ CCTOR])
  apply (rule trans)
   apply (rule \<tau>_pre.map_comp)
        apply (rule supp_id_bound bij_id)+
  unfolding o_id id_o
  apply (rule trans)
   apply (rule \<tau>_pre.map_comp)
        apply (rule supp_id_bound bij_id pick0_prems)+
  unfolding o_id id_o
  apply (rule trans)
   apply (rule \<tau>_pre.map_comp)
        apply (rule supp_id_bound bij_id pick0_prems)+
  unfolding o_id id_o
  apply (rule trans)
   apply (rule \<tau>_pre.map_cong)
             apply (rule supp_id_bound bij_id pick0_prems)+
       apply (rule refl)
      apply (rule refl)

  thm f.simps
  oops
*)

end
