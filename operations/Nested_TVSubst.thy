theory Nested_TVSubst
  imports "Binders.MRBNF_Recursor"
begin

(* binder_datatype 'a \<tau> =
  TyVar 'a
  | Arrow "'a \<tau>" "'a \<tau>" (infixr "\<rightarrow>" 40)
  | TyApp "'a \<tau>" "'a \<tau>" (infixr "@" 40)
  | TyAll \<alpha>::'a bound::"'a \<tau>" tybody::"'a \<tau>" binds \<alpha> in tybody (infixr "\<forall>_<_._" 30)

*)
ML \<open>
val tyctors = [
  (("TyVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("TyArr", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("TyAll", NONE), [@{typ 'bvar}, @{typ 'brec}])
]
val tyspec = {
  fp_b = @{binding "\<tau>"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = tyctors,
  map_b = @{binding vvsubst_\<tau>},
  tvsubst_b = @{binding tvsubst_\<tau>}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype tyspec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

thm \<tau>.strong_induct
thm \<tau>.set
thm \<tau>.map
thm \<tau>.subst

(* binder_datatype ('a,'b) term =
  Var 'b
| App "('a,'b) term" "('a,'b) term"
| Lam x::'b ty::"'a \<tau>" t::"('a,'b) term" binds x in t
| TyApp "('a,'b) term" "'a \<tau>"
| TyLam \<alpha>::'a body::"('a,'b) term" binds \<alpha> in body
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NONE), [@{typ 'bvar}, @{typ "'tyvar \<tau>"}, @{typ 'brec}]),
  (("TyApp", NONE), [@{typ 'rec}, @{typ "'tyvar \<tau>"}]),
  (("TyLam", NONE), [@{typ 'btyvar}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0], [0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[ML_print_depth=10000]]
declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val ((res, _, _, _), lthy) = MRBNF_Sugar.create_binder_type MRBNF_Util.Least_FP spec lthy;
  val ([(rec_mrbnf, vvsubst_res)], lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint [#map_b spec] I res lthy;
  val lthy = MRBNF_Def.register_mrbnf_raw "Nested_TVSubst.term" rec_mrbnf lthy
in lthy end\<close>
print_mrbnfs

abbreviation eta :: "'var \<Rightarrow> ('var::var_term_pre, 'tyvar::var_term_pre, 'a::var_term_pre, 'b::var_term_pre, 'c, 'd) term_pre" where
  "eta x \<equiv> Abs_term_pre (Inl (Inl x))"

(******* this is new ******************)
definition subst :: "('tyvar \<Rightarrow> 'tyvar \<tau>) \<Rightarrow> ('var::var_term_pre, 'tyvar::var_term_pre, 'var, 'tyvar, 'brec, 'rec) term_pre \<Rightarrow> ('var, 'tyvar, 'var, 'tyvar, 'brec, 'rec) term_pre" where
  "subst f y \<equiv> Abs_term_pre (map_sum id
    (map_sum (map_prod id (map_prod (tvsubst_\<tau> f) id))
    (map_sum (map_prod id (tvsubst_\<tau> f)) id)) (Rep_term_pre y))"

lemma subst_contained1: "set1_term_pre (subst f x) \<subseteq> set1_term_pre x"
  apply (unfold subst_def set1_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
  sum.set_map UN_singleton UN_empty2 Un_empty_left Un_empty_right image_id
)
  apply (rule subset_refl)
  done
lemma subst_contained2: "set2_term_pre (subst f x) \<subseteq> set2_term_pre x \<union> IImsupp_tvsubst_\<tau> f"
  apply (unfold subst_def set2_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
  sum.set_map UN_singleton UN_empty2 Un_empty_left Un_empty_right image_id prod.set_map
)
  apply (rule Abs_term_pre_cases[of x])
  apply hypsubst_thin
  apply (unfold Abs_term_pre_inverse[OF UNIV_I])
  apply (rule subsetI)
  apply ((erule UN_E imageE UnE)+, hypsubst, (unfold sum.set_map prod.set_map)?)+
  apply (rule iffD2[OF arg_cong2[OF refl UN_extend_simps(2), of "(\<in>)"]])
   apply (subst if_not_P)
    apply (rotate_tac)
    apply (erule contrapos_pn)
    apply (rotate_tac -1)
    apply (drule sym)
    apply (rotate_tac -1)
    apply (erule subst)
    apply (rule iffD2[OF notin_empty_eq_True])
    apply (rule TrueI)
   apply (rule UN_I)
  apply assumption
  done

(*************************************)

lemmas set_simp_thms = sum.set_map prod.set_map comp_def UN_empty UN_empty2 Un_empty_left Un_empty_right
  UN_singleton UN_single sum_set_simps prod_set_simps Diff_empty UN_Un empty_Diff

lemma eta_free: "set1_term_pre (eta x) = {x}"
  apply (unfold set1_term_pre_def Abs_term_pre_inverse[OF UNIV_I] set_simp_thms)
  apply (rule refl)
  done

lemma eta_inj: "eta x = eta y \<Longrightarrow> x = y"
  apply (unfold Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.simps)
  apply assumption
  done

lemma eta_compl_free: "x \<notin> range eta \<Longrightarrow> set1_term_pre x = {}"
  apply (unfold set1_term_pre_def set_simp_thms)
  apply (rule Abs_term_pre_cases[of x])
  apply hypsubst_thin
  apply (unfold image_iff bex_UNIV Abs_term_pre_inverse[OF UNIV_I] Abs_term_pre_inject[OF UNIV_I UNIV_I])
  apply (erule contrapos_np)
  apply (drule iffD2[OF ex_in_conv])
  apply (erule exE)
  apply (erule UN_E)
  apply (erule setl.cases)+
  apply hypsubst
  apply (rule exI)
  apply (rule refl)
  done

lemma eta_natural:
  fixes f1::"'var::var_term_pre \<Rightarrow> 'var" and f2::"'tyvar::var_term_pre \<Rightarrow> 'tyvar"
  and f3::"'a::var_term_pre \<Rightarrow> 'a" and f4::"'b::var_term_pre \<Rightarrow> 'b"
assumes "|supp f1| <o |UNIV::'var set|" "|supp f2| <o |UNIV::'tyvar set|"
        "bij f3" "|supp f3| <o |UNIV::'a set|" "bij f4" "|supp f4| <o |UNIV::'b set|"
      shows "map_term_pre f1 f2 f3 f4 f5 f6 \<circ> eta = eta \<circ> f1"
  apply (unfold comp_def map_sum.simps map_term_pre_def Abs_term_pre_inverse[OF UNIV_I])
  apply (rule refl)
  done

definition "VVr_term \<equiv> term_ctor \<circ> eta"

definition "SSupp_term f \<equiv> { x. f x \<noteq> VVr_term x }"
definition "IImsupp_1 f \<equiv> SSupp_term f \<union> \<Union>((FFVars_term1 \<circ> f) ` SSupp_term f)"
definition "IImsupp_2 f \<equiv> \<Union>((FFVars_term2 \<circ> f) ` SSupp_term f)"

type_synonym ('var, 'tyvar) SSfun = "'var \<Rightarrow> ('var, 'tyvar) term"
type_synonym ('var, 'tyvar) P = "('tyvar \<Rightarrow> 'tyvar \<tau>) \<times> ('var, 'tyvar) SSfun"

definition "isVVr x \<equiv> \<exists>a. x = VVr_term a"
definition "asVVr x \<equiv> (if isVVr x then SOME a. x = VVr_term a else undefined)"

definition compSS_1 :: "('tyvar::var_term_pre \<Rightarrow> 'tyvar) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar \<tau>) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar \<tau>)" where
  "compSS_1 f h \<equiv> rrename_\<tau> f \<circ> h \<circ> inv f"
definition compSS_2 :: "('var::var_term_pre \<Rightarrow> 'var) \<Rightarrow> ('tyvar::var_term_pre \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar) SSfun \<Rightarrow> ('var, 'tyvar) SSfun" where
  "compSS_2 f1 f2 h \<equiv> rrename_term f1 f2 \<circ> h \<circ> inv f1"

definition Uctor :: "('var::var_term_pre, 'tyvar::var_term_pre, 'var, 'tyvar,
  ('var, 'tyvar) term \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar) term),
  ('var, 'tyvar) term \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar) term)) term_pre \<Rightarrow> ('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar) term" where
  "Uctor y p \<equiv> case p of (f1, f2) \<Rightarrow> (
    if isVVr (term_ctor (map_term_pre id id id id fst fst y)) then
      f2 (asVVr (term_ctor (map_term_pre id id id id fst fst y)))
    else (
      term_ctor (map_term_pre id id id id ((\<lambda>R. R p) \<circ> snd) ((\<lambda>R. R p) \<circ> snd) (subst f1 y))
    ))"

definition "PFVars_1 p \<equiv> case p of (f1, f2) \<Rightarrow> IImsupp_1 f2"
definition "PFVars_2 p \<equiv> case p of (f1, f2) \<Rightarrow> IImsupp_tvsubst_\<tau> f1 \<union> IImsupp_2 f2"

definition "Pmap g1 g2 p \<equiv> case p of (f1, f2) \<Rightarrow> (compSS_1 g1 f1, compSS_2 g1 g2 f2)"

definition validP :: "('var::var_term_pre, 'tyvar::var_term_pre) P \<Rightarrow> bool" where
  "validP p \<equiv> case p of (f1, f2) \<Rightarrow> |SSupp_tvsubst_\<tau> f1| <o |UNIV::'tyvar set| \<and> |SSupp_term f2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"

(**********************************************************************)
(*                               PROOFS                               *)
(**********************************************************************)

lemma VVr_inj: "VVr_term x = VVr_term y \<Longrightarrow> x = y"
  apply (unfold VVr_term_def comp_def)
  apply (rule eta_inj)
  apply (drule term.TT_injects0[THEN iffD1])
  apply (erule exE conjE)+
  apply (drule trans[rotated])
   apply (rule sym)
   apply (rule trans)
    apply (rule fun_cong[OF eta_natural, unfolded comp_def])
         apply (assumption | rule supp_id_bound bij_id)+
   apply (rule arg_cong[OF id_apply])
  apply assumption
  done

lemma asVVr_VVr: "asVVr (VVr_term x) = x"
  apply (unfold asVVr_def isVVr_def)
  apply (subst if_P)
   apply (rule exI)
   apply (rule refl)
  apply (rule some_equality)
   apply (rule refl)
  apply (rule sym)
  apply (erule VVr_inj)
  done

lemma FFVars_subset1:
  fixes p::"('var::var_term_pre, 'tyvar::var_term_pre) P"
    and y::"('var, 'tyvar, 'var, 'tyvar, _, _) term_pre"
  shows
"validP p \<Longrightarrow> set3_term_pre y \<inter> PFVars_1 p = {} \<Longrightarrow>
  (\<And>t pu p. validP p \<Longrightarrow> (t, pu) \<in> set5_term_pre y \<union> set6_term_pre y \<Longrightarrow> FFVars_term1 (pu p) \<subseteq> FFVars_term1 t \<union> PFVars_1 p) \<Longrightarrow>
  FFVars_term1 (Uctor y p) \<subseteq> FFVars_term1 (term_ctor (map_term_pre id id id id fst fst y)) \<union> PFVars_1 p"
  subgoal premises prems
    apply (unfold Uctor_def case_prod_beta)
(* REPEAT_DETERM *)
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
     apply (unfold isVVr_def)[1]
     apply (erule exE)
     apply (drule sym)
     apply (erule subst)
     apply (unfold asVVr_VVr)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FFVars_term1])
       apply assumption
      apply (rule Un_upper1)
    apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_1_def case_prod_beta IImsupp_1_def SSupp_term_def)[1]
     apply (rule UnI2)
     apply (rule UN_I)
      apply (erule CollectI)
     apply (rule iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]])
     apply assumption
    apply (unfold if_not_P)
  (* END REPEAT_DETERM *)
    apply (unfold term.FFVars_cctors)
    apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id image_comp comp_def)
    apply (rule Un_mono')+

end