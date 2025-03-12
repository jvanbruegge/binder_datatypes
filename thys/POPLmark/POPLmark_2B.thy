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

type_synonym ('tv, 'v) \<Gamma>\<^sub>t = "('tv, 'tv + 'v) \<Gamma>"

inductive wf_ctxt :: "('tv::var, 'v::var) \<Gamma>\<^sub>t \<Rightarrow> bool" ("\<turnstile> _ OK" [70] 100) where
  wf_ctxt_Nil[intro]: "\<turnstile> [] OK"
| wf_ctxt_Cons[intro!]: "\<lbrakk> x \<notin> dom \<Gamma> ; FVars_typ T \<subseteq> Inl -` dom \<Gamma>; \<turnstile> \<Gamma> OK \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>\<^bold>,x<:T OK"

inductive_cases
  wf_ctxtE[elim]: "\<turnstile> \<Gamma> OK"
  and wf_ctxt_ConsE[elim!]: "\<turnstile> (a#\<Gamma>) OK"

definition proj_ctxt :: "('tv::var, 'v::var) \<Gamma>\<^sub>t \<Rightarrow> 'tv \<Gamma>\<^sub>\<tau>" where
  "proj_ctxt = List.map_filter (\<lambda>(x, T). case x of Inl X \<Rightarrow> Some (X, T) | _ \<Rightarrow> None)"

lemma wf_ty_proj_ctxt: "\<turnstile> \<Gamma> OK \<Longrightarrow> \<turnstile> proj_ctxt \<Gamma> ok"
  apply (induct \<Gamma>)
   apply (auto simp: proj_ctxt_def map_filter_def vimage_def image_def split_beta subset_eq split: sum.splits)
  apply fastforce
  apply (metis Inl_inject Inr_Inl_False prod.exhaust_sel)
  done

inductive typing :: "('tv::var, 't::var) \<Gamma>\<^sub>t \<Rightarrow> ('tv, 't) trm \<Rightarrow> 'tv typ \<Rightarrow> bool" ("_ \<^bold>\<turnstile> _ \<^bold>: _" [30,29,30] 30) where
  TVar: "\<turnstile> \<Gamma> OK \<Longrightarrow> (Inr x, T) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Var x \<^bold>: T"
| TAbs: "\<Gamma> \<^bold>, Inr x <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Abs x T1 t \<^bold>: T1 \<rightarrow> T2"
| TApp: "\<Gamma> \<^bold>\<turnstile> t1 \<^bold>: T11 \<rightarrow> T12 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t2 \<^bold>: T11 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> App t1 t2 \<^bold>: T12"
| TTAbs: "\<Gamma> \<^bold>, Inl X <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> TAbs X T1 t \<^bold>:  \<forall>X <: T1. T2"
| TTApp: "\<Gamma> \<^bold>\<turnstile> t1 \<^bold>: \<forall>X <: T11. T12 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> T2 <: T11 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> TApp t1 T2 \<^bold>: tvsubst_typ (TyVar(X := T2)) T12"
| TSub: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: S \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t \<^bold>: T"

lemma typing_wf_ctxt: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> OK"
  by (induct rule: typing.induct) auto
lemma typing_wf_ty: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> proj_ctxt \<Gamma> ok"
  by (rule wf_ty_proj_ctxt) (rule typing_wf_ctxt)

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

lemma TAbs_inject:
  fixes t u :: "('tv :: var, 'v :: var) trm"
  shows "TAbs X T t = TAbs Y U u \<longleftrightarrow> T = U \<and> (\<exists>f. bij (f::'tv::var \<Rightarrow> 'tv) \<and> |supp f| <o |UNIV::'tv set| \<and> id_on (FTVars t - {X}) f \<and> f X = Y \<and> permute_trm f id t = u)"
    apply (unfold TAbs_def trm.TT_inject0
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
    apply (rule exI)
    apply (rule exI[of _ id])
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  done

lemma in_context_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "(x, T) \<in> set \<Gamma> \<Longrightarrow> (f2 x, permute_typ f1 T) \<in> set (map (map_prod f2 (permute_typ f1)) \<Gamma>)"
  using assms by auto

lemma permute_tusubst[equiv]:
  fixes f::"'a::var \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "permute_typ f (tvsubst_typ (TyVar(X := T2)) T1) = tvsubst_typ (TyVar(f X := permute_typ f T2)) (permute_typ f T1)"
  apply (rule trans)
   apply (rule trans[OF comp_apply[symmetric] typ.tvsubst_permutes[THEN fun_cong]])
     apply (rule assms)+
  apply (metis SSupp_typ_TyVar SSupp_typ_fun_upd_le card_of_mono1 emp_bound infinite_UNIV insert_bound ordLeq_ordLess_trans)
  apply (unfold fun_upd_def comp_def)
  apply (rule arg_cong2[OF _ refl, of _ _ tvsubst_typ])
  apply (rule ext)
  subgoal for x
    apply (cases "x = f X")
    using assms apply auto
    done
  done

lemma wf_ctxt_FFVars: "\<turnstile> \<Gamma> OK \<Longrightarrow> a \<in> FFVars_ctxt \<Gamma> \<Longrightarrow> Inl a \<in> dom \<Gamma>"
  by (induction \<Gamma>) auto
lemma typing_fresh_ty_extend: "\<Gamma> \<^bold>, Inl x <: U \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> x \<notin> Inl -` dom \<Gamma> \<union> FFVars_ctxt \<Gamma> \<and> x \<notin> FVars_typ U"
  by (metis Pair_inject UnE subset_vimage_iff typing_wf_ctxt vimageD wf_ctxt_FFVars wf_ctxt_ConsE)
(*
binder_inductive (no_auto_equiv) typing
  subgoal premises prems for R B1 B2 \<sigma>1 \<sigma>2 \<Gamma> t T
    using prems(5)
    sorry
  subgoal premises prems for R B1 B2 \<Gamma> t T
    unfolding ex_simps conj_disj_distribL ex_disj_distrib
    using prems(3)
    apply -
    apply (elim disjE conjE exE; hypsubst_thin)
    subgoal for x T' \<Gamma>'
      by auto
    subgoal for \<Gamma>' x T1 t T2
      apply (rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{x} \<union> FVars t \<union> Inr -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: trm.Un_bound trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inr lfset.UNIV_cinfinite)
      subgoal for y
        apply (rule exI[of _ "{}"]; simp)
        apply (rule exI[of _ "{y}"]; simp add: Abs_inject)
        apply (rule conjI)
        apply (metis imageI setr.cases)
        apply (rule exI[of _ "permute_trm id (id(x := y, y := x)) t"] conjI exI[of _ "id(x := y, y := x)"])+
         apply (simp_all add: id_on_def setr.simps)
        apply (frule prems(1)[THEN typing_wf_ctxt])
        apply (frule prems(1)[THEN typing_wf_ty])
        apply (frule prems(2)[of id "id(x := y, y := x)", rotated -1])
        apply (auto simp: image_iff intro!: list.map_ident_strong sum.map_ident_strong
          elim!: arg_cong[where f = "\<lambda>x. R x _ _", THEN iffD1, rotated])
        apply (metis fst_conv setr.cases)+
        done
      done
    subgoal for \<Gamma>' t T' _ u
      by auto
    subgoal for \<Gamma>' X T1 t T2
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FVars_typ T1  \<union> FVars_typ T2 \<union> FTVars t \<union> FFVars_ctxt \<Gamma> \<union> Inl -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: typ.Un_bound typ.UN_bound typ.set_bd_UNIV trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inl lfset.UNIV_cinfinite)
      subgoal for Y
        apply (rule exI[of _ "{Y}"]; simp add: TAbs_inject)
        apply (rule conjI)
        apply (metis imageI setl.cases)
        apply (rule exI[of _ "permute_trm (id(X := Y, Y := X)) id t"] conjI exI[of _ "id(X := Y, Y := X)"])+
          apply (simp_all add: id_on_def) [2]
        apply (rule exI[of _ "permute_typ (id(X := Y, Y := X)) T2"])
        apply (frule prems(1)[THEN typing_fresh_ty_extend])
        apply (frule prems(2)[of "(id(X := Y, Y := X))" id, rotated -1])
            apply (auto simp add: typ_inject id_on_def dom_def subset_eq image_iff
            intro!: list.map_ident_strong sum.map_ident_strong typ.permute_cong_id exI[of _ "id(X := Y, Y := X)"]
            elim!: arg_cong2[where f = "\<lambda>x y. R x y _", THEN iffD1, rotated 2])
           apply (metis fst_conv setl.cases)
          apply (metis fst_conv setl.cases)
         apply fastforce
        apply fastforce
        done
      done
    subgoal for \<Gamma>' t X T11 T12 T2
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FVars_typ T11  \<union> FVars_typ T12  \<union> FVars_typ T2 \<union> FTVars t \<union> FFVars_ctxt \<Gamma> \<union> Inl -` dom \<Gamma>"]])
       apply (auto simp: insert_bound infinite_UNIV intro!: typ.Un_bound typ.UN_bound typ.set_bd_UNIV trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inl lfset.UNIV_cinfinite)
      subgoal for Y
        apply (rule exI[of _ "{Y}"]; simp add: TAbs_inject)
        apply (intro conjI)
          apply (metis imageI setl.cases)

        apply (subst typ.subst)
        find_theorems tvsubst_typ
        apply (rule exI[of _ "T11"] conjI exI[of _ "id(X := Y, Y := X)"])+
          apply (simp_all add: id_on_def) [2]
      apply simp
    sorry
  sorry
        apply (simp add: rev_image_eqI)
        find_theorems "permute_typ _ ?x = ?x"
        apply (rule context_map_cong_id[unfolded map_context_def, simplified])
        thm context_map_cong_id[unfolded map_context_def, simplified]
        thm arg_cong2[where f = "\<lambda>x y. R x y _ _", THEN iffD1, rotated 2]
        apply (rule exI[of _ "{}"]; simp add: Abs_inject)
      apply (rule exI[of _ "{}"]; simp)
    apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)
    done
  done
*)
end
