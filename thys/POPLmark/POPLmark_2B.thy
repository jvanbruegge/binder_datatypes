theory POPLmark_2B
imports POPLmark_1B
begin

binder_datatype (FTVars: 'tv, FVars: 'v) trm = Var 'v
  | Abs x::'v "'tv typ" t::"('tv, 'v) trm" binds x in t
  | App "('tv, 'v) trm" "('tv, 'v) trm"
  | TAbs X::'tv "'tv typ" t::"('tv, 'v) trm" binds X in t
  | TApp "('tv, 'v) trm" "'tv typ"
print_theorems

inductive "value" where
  "value (Abs x T t)"
| "value (TAbs X T t)"

inductive typing :: "('a, 'b::var) \<Gamma> \<Rightarrow> 'a::var \<Gamma>\<^sub>\<tau> \<Rightarrow> ('a, 'b) trm \<Rightarrow> 'a typ \<Rightarrow> bool" ("_ \<^bold>| _ \<^bold>\<turnstile> _ \<^bold>: _" [30,29,29,30] 30) where
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

lemma Abs_inject:
  fixes t u :: "('tv :: var, 'v :: var) trm"
  shows "Abs x T t = Abs y U u \<longleftrightarrow> T = U \<and> (\<exists>f. bij (f::'v::var \<Rightarrow> 'v) \<and> |supp f| <o |UNIV::'v set| \<and> id_on (FVars t - {x}) f \<and> f x = y \<and> permute_trm id f t = u)"
    apply (unfold Abs_def trm.TT_inject0
      set3_trm_pre_def set4_trm_pre_def set5_trm_pre_def comp_def Abs_trm_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_trm_pre_def
      prod.map_id set2_typ_pre_def prod_set_simps prod.set_map UN_single Abs_trm_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp typ.map_id
    )
  apply safe
  subgoal for f g
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  subgoal for f
    apply (rule exI[of _ id])
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  done

declare trm.permute[equiv]

lemma in_context_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "(x, T) \<in> set \<Gamma> \<Longrightarrow> (f2 x, permute_typ f1 T) \<in> set (map (map_prod f2 (permute_typ f1)) \<Gamma>)"
  using assms by auto

thm equiv

(* TODO use permute_typ in trm.permute *)

binder_inductive (verbose) typing
  subgoal premises prems for R B1 B2 \<Gamma> \<Delta> t T
    (*apply (tactic \<open>refreshability_tac true
      [@{term "\<lambda>\<Gamma>. dom \<Gamma> \<union> FFVars_ctxt \<Gamma>"}, @{term "\<lambda>\<Delta>. dom \<Delta> \<union> FFVars_ctxt \<Delta>"}, @{term "\<lambda>t :: term. FVars t \<union> FTVars t"}, @{term "FVars_typ :: type \<Rightarrow> var set"}]
      [@{term "\<lambda>f. permute_trm f f :: term \<Rightarrow> term"}, @{term "permute_typ :: (var \<Rightarrow> var) \<Rightarrow> type \<Rightarrow> type"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]
      [NONE, SOME [NONE, SOME 2, NONE, NONE, SOME 0, NONE], NONE, NONE, NONE, NONE]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound insert_bound ID.set_bd trm.Un_bound trm.UN_bound trm.set_bd_UNIV typ.set_bd_UNIV infinite_UNIV}
      @{thms Abs_inject image_iff} @{thms trm.permute_cong}
      @{thms id_onD} @{context}\<close>)*)
    sorry
  done

end
