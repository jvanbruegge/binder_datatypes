theory POPLmark_2B
imports POPLmark_1B
begin

binder_datatype (FTVars: 'tv, FVars: 'v) trm = Var 'v
  | Abs x::'v "'tv typ" t::"('tv, 'v) trm" binds x in t
  | App "('tv, 'v) trm" "('tv, 'v) trm"
  | TAbs X::'tv "'tv typ" t::"('tv, 'v) trm" binds X in t
  | TApp "('tv, 'v) trm" "'tv typ"

print_theorems
(*TODO bindings FVars not used*)
type_synonym "term" = "(var, var) trm"

inductive "value" where
  "value (Abs x T t)"
| "value (TAbs X T t)"

inductive typing :: "\<Gamma>\<^sub>\<tau> \<Rightarrow> \<Gamma>\<^sub>\<tau> \<Rightarrow> term \<Rightarrow> type \<Rightarrow> bool" ("_ \<^bold>| _ \<^bold>\<turnstile> _ \<^bold>: _" [30,29,29,30] 30) where
  TVar: "(x, T) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> Var x \<^bold>: T"
| TAbs: "\<Gamma> \<^bold>, x <: T1 \<^bold>| \<Delta> \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> Abs x T1 t \<^bold>: T1 \<rightarrow> T2"
| TApp: "\<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> t1 \<^bold>: T11 \<rightarrow> T12 \<Longrightarrow> \<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> t2 \<^bold>: T11 \<Longrightarrow> \<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> App t1 t2 \<^bold>: T12"
| TTAbs: "\<Gamma> \<^bold>| \<Delta> \<^bold>, X <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> TAbs X T1 t \<^bold>:  \<forall>X <: T1. T2"
| TTApp: "\<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> t1 \<^bold>: \<forall>X <: T11. T12 \<Longrightarrow> \<Delta> \<turnstile> T2 <: T11 \<Longrightarrow> \<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> TApp t1 T2 \<^bold>: tvsubst_typ (TyVar(X := T2)) T12"
| TSub: "\<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> t \<^bold>: S \<Longrightarrow> \<Delta> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<^bold>| \<Delta> \<^bold>\<turnstile> t \<^bold>: T"

lemma VVr_eq_TyVar[simp]: "tvVVr_tvsubst_typ a = TyVar a"
  unfolding tvVVr_tvsubst_typ_def Var_def comp_def tv\<eta>_typ_tvsubst_typ_def TyVar_def
  by (rule refl)

lemma SSupp_typ_TyVar[simp]: "SSupp_typ TyVar = {}"
  unfolding SSupp_typ_def by simp

lemma SSupp_typ_fun_upd_le: "SSupp_typ (f(X := T)) \<subseteq> insert X (SSupp_typ f)"
  unfolding SSupp_typ_def by auto

lemma SSupp_typ_fun_upd_bound[simp]: "|SSupp_typ (f(X := T))| <o |UNIV :: var set| \<longleftrightarrow> |SSupp_typ f| <o |UNIV :: var set|"
  apply safe
   apply (metis SSupp_typ_fun_upd_le card_of_mono1 fun_upd_idem_iff fun_upd_upd infinite_UNIV insert_bound ordLeq_ordLess_trans)
  apply (meson SSupp_typ_fun_upd_le card_of_mono1 infinite_UNIV insert_bound ordLeq_ordLess_trans)
  done

binder_inductive typing
subgoal for R B \<sigma> \<Gamma> T1 T2
    unfolding split_beta
    by (elim disj_forward exE)
      (auto simp add: isPerm_def supp_inv_bound map_context_def[symmetric] typ.vvsubst_permute trm.vvsubst_permute in_context_eqvt ty.equiv[folded map_context_def]
        typ.permute_comp trm.permute_comp typ.FVars_permute trm.FVars_permute trm.permute_id wf_eqvt extend_eqvt lfset.set_map lfin_map_lfset induct_rulify_fallback
        fun_eq_iff typ.tvsubst_permutes[THEN fun_cong, simplified] intro!: arg_cong[where f = "\<lambda>f. tvsubst_typ f _"]
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((drule spec2)+, (drule mp)?, assumption)
        | ((rule exI[of _ "permute_typ \<sigma> _"])+, (rule conjI)?))+
  subgoal premises prems for R B \<Gamma> \<Delta> t T

    find_consts name: FVars
    apply (tactic \<open>refreshability_tac true
      [@{term "\<lambda>\<Gamma>. dom \<Gamma> \<union> FFVars_ctxt \<Gamma>"}, @{term "\<lambda>\<Delta>. dom \<Delta> \<union> FFVars_ctxt \<Delta>"}, @{term "\<lambda>t :: term. FVars_trm1 t \<union> FVars_trm2 t"}, @{term "FVars_typ :: type \<Rightarrow> var set"}]
      [@{term "\<lambda>f. permute_trm f f :: term \<Rightarrow> term"}, @{term "permute_typ :: (var \<Rightarrow> var) \<Rightarrow> type \<Rightarrow> type"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]
      [NONE, SOME [NONE, SOME 2, NONE, NONE, SOME 0, NONE], NONE, NONE, NONE, NONE]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound insert_bound ID.set_bd trm.Un_bound trm.UN_bound trm.set_bd_UNIV typ.set_bd_UNIV infinite_UNIV}
      @{thms typ_inject image_iff} @{thms typ.permute_cong_id context_map_cong_id map_idI}
      @{thms } @{context}\<close>)
  done

end