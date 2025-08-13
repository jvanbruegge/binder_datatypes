theory POPLmark_2B
  imports POPLmark_1B Pattern "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"
begin

binder_datatype (FTVars: 'tv, FVars: 'v) trm =
    Var 'v
  | Abs x::'v "'tv typ" t::"('tv, 'v) trm" binds x in t
  | App "('tv, 'v) trm" "('tv, 'v) trm"
  | TAbs X::'tv "'tv typ" t::"('tv, 'v) trm" binds X in t
  | TApp "('tv, 'v) trm" "'tv typ"
  | Rec "(label, ('tv, 'v) trm) lfset"
  | Proj "('tv, 'v) trm" label
  | Let "('tv, p::'v) pat" "('tv, 'v) trm" t::"('tv, 'v) trm" binds p in t
print_theorems

thm trm.subst

abbreviation "tvsubst f1 f2 \<equiv> tvsubst_trm f2 f1"

inductive "value" where
  "value (Abs x T t)"
| "value (TAbs X T t)"
| "(\<forall>v \<in> values XX. value v) \<Longrightarrow> value (Rec XX)"

lemma value_equiv[equiv]:
  fixes \<sigma>1::"'tv::var \<Rightarrow> 'tv" and \<sigma>2::"'v::var \<Rightarrow> 'v"
  assumes "bij \<sigma>1" "|supp \<sigma>1| <o |UNIV::'tv set|" "bij \<sigma>2" "|supp \<sigma>2| <o |UNIV::'v set|"
  shows "value x \<Longrightarrow> value (permute_trm \<sigma>1 \<sigma>2 x)"
  apply (induction rule: value.induct)
  using assms by (auto simp: lfset.set_map intro!: value.intros)

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

lemma wf_ctxt_equiv[equiv]:
  fixes \<sigma>1::"'tv::var \<Rightarrow> 'tv" and \<sigma>2::"'v::var \<Rightarrow> 'v"
  assumes "bij \<sigma>1" "|supp \<sigma>1| <o |UNIV::'tv set|" "bij \<sigma>2" "|supp \<sigma>2| <o |UNIV::'v set|"
  shows "\<turnstile> \<Gamma> OK \<Longrightarrow> \<turnstile> map (map_prod (map_sum \<sigma>1 \<sigma>2) (permute_typ \<sigma>1)) \<Gamma> OK"
proof (induction \<Gamma> rule: wf_ctxt.induct)
  case (wf_ctxt_Cons x \<Gamma> T)
  have 1: "bij (map_sum \<sigma>1 \<sigma>2)"
    apply (rule o_bij)
     apply (rule trans)
      apply (rule ext)
      apply (rule trans[OF comp_apply])
      apply (rule sum.map_comp[of "inv \<sigma>1" "inv \<sigma>2"])
     apply (auto simp: assms sum.map_id sum.map_comp)
    done
  show ?case
    apply simp
    apply (rule wf_ctxt.wf_ctxt_Cons)
      apply (unfold list.set_map image_comp)[1]
      apply (insert wf_ctxt_Cons(1))[1]
      apply (simp add: "1" bij_implies_inject image_iff)
     apply (auto simp: assms typ.FVars_permute)
    using image_iff wf_ctxt_Cons(2) apply fastforce
    by (rule wf_ctxt_Cons(4))
qed auto

inductive pat_typing :: "('tv :: var, 't :: var) pat \<Rightarrow> 'tv typ \<Rightarrow> ('tv, 't) \<Gamma>\<^sub>t \<Rightarrow> bool" ("\<turnstile> _ : _ \<rightarrow> _" [30,29,30] 30) where
  PVar: "\<turnstile> PVar x T : T \<rightarrow> \<emptyset> \<^bold>, Inr x <: T"
| PRec: "nonrep_PRec PP \<Longrightarrow> labels PP = labels TT \<Longrightarrow> (\<And>l P T. (l, P) \<in>\<in> PP \<Longrightarrow> (l, T) \<in>\<in> TT \<Longrightarrow> \<turnstile> P : T \<rightarrow> \<Delta> l) \<Longrightarrow> xs = labelist TT \<Longrightarrow> \<turnstile> PRec PP : TRec TT \<rightarrow> List.concat (map \<Delta> xs)"

inductive typing :: "('tv::var, 't::var) \<Gamma>\<^sub>t \<Rightarrow> ('tv, 't) trm \<Rightarrow> 'tv typ \<Rightarrow> bool" ("_ \<^bold>\<turnstile> _ \<^bold>: _" [30,29,30] 30) where
  TVar: "\<turnstile> \<Gamma> OK \<Longrightarrow> (Inr x, T) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Var x \<^bold>: T"
| TAbs: "\<Gamma> \<^bold>, Inr x <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Abs x T1 t \<^bold>: T1 \<rightarrow> T2"
| TApp: "\<Gamma> \<^bold>\<turnstile> t1 \<^bold>: T11 \<rightarrow> T12 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t2 \<^bold>: T11 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> App t1 t2 \<^bold>: T12"
| TTAbs: "\<Gamma> \<^bold>, Inl X <: T1 \<^bold>\<turnstile> t \<^bold>: T2 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> TAbs X T1 t \<^bold>:  \<forall>X <: T1. T2"
| TTApp: "\<Gamma> \<^bold>\<turnstile> t1 \<^bold>: \<forall>X <: T11. T12 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> T2 <: T11 \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> TApp t1 T2 \<^bold>: tvsubst_typ (TyVar(X := T2)) T12"
| TSub: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: S \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t \<^bold>: T"
| TRec: "\<turnstile> \<Gamma> OK \<Longrightarrow> rel_lfset id (\<lambda>t T. \<Gamma> \<^bold>\<turnstile> t \<^bold>: T) XX TT \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Rec XX \<^bold>: TRec TT"
| TProj: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: TRec TT \<Longrightarrow> (l, T) \<in>\<in> TT \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Proj t l \<^bold>: T"
| TLet: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> p : T \<rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> u \<^bold>: U  \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> Let p t u \<^bold>: U"

lemmas [simp] = map_filter_simps

lemma typing_wf_ctxt: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> OK"
  by (induct rule: typing.induct) auto
lemma typing_wf_ty: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> proj_ctxt \<Gamma> ok"
  by (rule wf_ty_proj_ctxt) (rule typing_wf_ctxt)

lemma proj_ctxt_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "map (map_prod f1 (permute_typ f1)) (proj_ctxt \<Gamma>) = proj_ctxt (map (map_prod (map_sum f1 f2) (permute_typ f1)) \<Gamma>)"
  by (induction \<Gamma>) (auto split: sum.splits simp: proj_ctxt_def case_prod_beta)

lemma ty_proj_ctxt_equiv[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "proj_ctxt \<Gamma> \<turnstile> T2 <: T1 \<Longrightarrow> proj_ctxt (map (map_prod (map_sum f1 f2) (permute_typ f1)) \<Gamma>) \<turnstile> permute_typ f1 T2 <: permute_typ f1 T1"
  apply (subst proj_ctxt_equiv[OF assms, symmetric])
  apply (erule ty.equiv[rotated -1])
   apply (rule assms)+
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

lemma Let_inject:
  fixes t t' u u' :: "('tv :: var, 'v :: var) trm"
  shows "Let p t u = Let p' t' u' \<longleftrightarrow> t = t' \<and> (\<exists>f. bij (f::'v::var \<Rightarrow> 'v) \<and> |supp f| <o |UNIV::'v set| \<and> id_on (FVars u - PVars p) f \<and> vvsubst_pat id f p = p' \<and> permute_trm id f u = u')"
    apply (unfold Let_def trm.TT_inject0
      set3_trm_pre_def set4_trm_pre_def set5_trm_pre_def comp_def Abs_trm_pre_inverse[OF UNIV_I] map_sum.simps sum_set_simps
      cSup_singleton Un_empty_left Un_empty_right Union_empty image_empty empty_Diff map_trm_pre_def
      prod.map_id set2_typ_pre_def prod_set_simps prod.set_map UN_single Abs_trm_pre_inject[OF UNIV_I UNIV_I]
      sum.inject prod.inject map_prod_simp typ.map_id
    )
  apply safe
  subgoal for f g
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  subgoal for f g
    apply (auto simp: id_on_def intro!: trm.permute_cong)
    done
  subgoal for f
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
   apply (rule trans[OF comp_apply[symmetric] typ.tvsubst_permute[THEN fun_cong]])
     apply (rule assms)+
  apply simp
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

lemmas [equiv] = typ.tvsubst_permute[THEN fun_cong, unfolded comp_def]

lemma permute_TyVar[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|"
  shows "permute_typ f1 \<circ> TyVar \<circ> inv f1 = TyVar"
  using assms by (auto simp: comp_def)
lemma permute_Var[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_trm f1 f2 \<circ> Var \<circ> inv f2 = Var"
  using assms by (auto simp: comp_def)

lemma fun_upd_comp_TyVar[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|"
  shows "permute_typ f1 \<circ> TyVar(X := T) \<circ> inv f1 = (TyVar(f1 X := permute_typ f1 T))"
  using assms by (auto simp: comp_def fun_upd_def split!: if_splits)
lemma fun_upd_comp_Var[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_trm f1 f2 \<circ> Var(x := v) \<circ> inv f2 = (Var(f2 x := permute_trm f1 f2 v))"
  using assms by (auto simp: comp_def fun_upd_def split!: if_splits)

lemmas [simp] = trm.set_bd_UNIV

lemma permute_tusubst_trm_trm[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_trm f1 f2 (tvsubst (Var(x := v)) TyVar t) = tvsubst (Var(f2 x := permute_trm f1 f2 v)) TyVar (permute_trm f1 f2 t)"
  apply (rule trans[OF comp_apply[symmetric] trans[OF trm.tvsubst_permute[OF assms, THEN fun_cong]]])
  by (auto simp: assms trm.tvsubst_permute)

lemma permute_tusubst_trm_typ[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_trm f1 f2 (tvsubst Var (TyVar(X := T)) t) = tvsubst Var (TyVar(f1 X := permute_typ f1 T)) (permute_trm f1 f2 t)"
  apply (rule trans[OF comp_apply[symmetric] trans[OF trm.tvsubst_permute[OF assms, THEN fun_cong]]])
  by (auto simp: assms trm.tvsubst_permute)

lemma Forall_eq_tvsubst_typ:
assumes il: "Forall (X :: 'a ::var) T2 T1 = Forall Y T2 T1'"
shows "tvsubst_typ (TyVar (X:=T2)) T1 = tvsubst_typ (TyVar (Y:=T2)) T1'"
proof-
  obtain f where f: "bij f" "|supp f| <o |UNIV:: 'a :: var set|" "id_on (FVars_typ T1 - {X}) f"
  and 0: "Y = f X" "T1' = permute_typ f T1" using il[unfolded typ_inject] by auto
  show ?thesis unfolding 0
    apply (subst typ.vvsubst_permute[symmetric], (rule f)+)
    apply (subst typ.map_is_Sb)
     apply (rule f)
    subgoal apply(subst trans[OF comp_apply[symmetric] typ.Sb_comp[THEN fun_cong]])
        apply (auto simp: f comp_assoc[symmetric] typ.Sb_comp_Inj)
      apply (rule typ.Sb_cong)
        apply (auto simp: f bij_implies_inject)
      using f(3) id_onD by fastforce
    done
qed

lemma in_context_equiv_Inr[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "(Inr (f2 x), permute_typ f1 T) \<in> map_prod (map_sum f1 f2) (permute_typ f1) ` set \<Gamma> \<longleftrightarrow> (Inr x, T) \<in> set \<Gamma>"
  using assms apply auto
  subgoal for y T'
    apply (rule sum.exhaust[of y])
     apply auto
    by (metis bij_pointE typ.permute_bij)
  by (metis map_prod_imageI map_sum.simps(2))

lemma extend_equiv_sum[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "bij f2"
  shows "map (map_prod (map_sum f1 f2) (permute_typ f1)) (\<Gamma>\<^bold>,x<:T) = map (map_prod (map_sum f1 f2) (permute_typ f1)) \<Gamma>\<^bold>, map_sum f1 f2 x <: permute_typ f1 T"
  by simp
lemma concat_equiv_sum[equiv]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "bij f2"
  shows "map (map_prod (map_sum f1 f2) (permute_typ f1)) (\<Gamma>\<^bold>,\<Delta>) = map (map_prod (map_sum f1 f2) (permute_typ f1)) \<Gamma>\<^bold>, map (map_prod (map_sum f1 f2) (permute_typ f1)) \<Delta>"
  by simp
lemmas [equiv] = map_sum.simps map_prod_simp

lemma pat_typing_equiv[equiv]:
  assumes "bij f" "|supp f| <o |UNIV :: 'tv::var set|"
    "bij g" "|supp g| <o |UNIV :: 'v::var set|"
  shows "\<turnstile> (p :: ('tv, 'v) pat) : T \<rightarrow> \<Delta> \<Longrightarrow>
    \<turnstile> vvsubst_pat f g p : permute_typ f T \<rightarrow> map (map_prod (map_sum f g) (permute_typ f)) \<Delta>"
  apply (induct p T \<Delta> rule: pat_typing.induct)
   apply (auto simp: assms typ.vvsubst_permute map_concat lfin_map_lfset
     intro!: pat_typing.intros)
  apply (auto simp: nonrep_PRec_def lfset.set_map lfin_map_lfset vvsubst_pat_tvsubst_pat assms PVars_tvsubst_pat)
  apply (metis Int_emptyD assms(3) bij_implies_inject)
  done

lemma HELP1[equiv]: "bij \<sigma>1a \<Longrightarrow>
    |supp \<sigma>1a| <o |UNIV :: 'tv::var set| \<Longrightarrow>
    bij \<sigma>2a \<Longrightarrow>
    |supp \<sigma>2a| <o |UNIV :: 'v::var set| \<Longrightarrow>
    rel_lfset id
     (\<lambda>x2 x3.
         Ra (map (map_prod (map_sum (inv \<sigma>1a) (inv \<sigma>2a)) (permute_typ (inv \<sigma>1a)))
              (map (map_prod (map_sum \<sigma>1a \<sigma>2a) (permute_typ \<sigma>1a)) \<Gamma>'))
          (permute_trm (inv \<sigma>1a) (inv \<sigma>2a) x2) (permute_typ (inv \<sigma>1a) x3))
     (map_lfset id (permute_trm \<sigma>1a \<sigma>2a) XXa) (map_lfset id (permute_typ \<sigma>1a) TTa) \<longleftrightarrow>
    rel_lfset id (Ra \<Gamma>') (XXa :: (string, ('tv, 'v) trm) lfset) TTa"
  by (auto simp: o_def prod.map_comp sum.map_comp sum.map_ident
       typ.permute_comp typ.permute_id[unfolded id_def] supp_inv_bound
       trm.permute_comp trm.permute_id[unfolded id_def] lfset.rel_map
       elim!: lfset.rel_mono_strong)

lemma pat_typing_dom: "\<turnstile> p : T \<rightarrow> \<Delta> \<Longrightarrow> dom \<Delta> = Inr ` PVars p"
  apply (induct p T \<Delta> rule: pat_typing.induct)
   apply (auto simp: set_labelist image_iff set_eq_iff labels_lfin_iff Bex_def values_lfin_iff)
   apply (smt (verit, del_insts) fstI image_iff image_subset_iff)+
  done

lemma wf_ctxt_concat_disjoint: "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> \<Gamma> \<bottom> \<Delta>"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then show ?case
    by (cases a) auto
qed simp

binder_inductive typing
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
       apply (auto simp: insert_bound_UNIV infinite_UNIV intro!: trm.Un_bound trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inr lfset.UNIV_cinfinite)
      subgoal for y
        apply (rule exI[of _ "{}"]; simp)
        apply (rule exI[of _ "{y}"]; simp add: Abs_inject)
        apply (rule conjI)
        apply (metis imageI setr.cases)
        apply (frule prems(1)[THEN typing_wf_ctxt])
        apply (frule prems(1)[THEN typing_wf_ty])
        apply (frule prems(2)[of id "x \<leftrightarrow> y", rotated -1])
        apply (auto simp: image_iff intro!: list.map_ident_strong sum.map_ident_strong
          elim!: arg_cong[where f = "\<lambda>x. R x _ _", THEN iffD1, rotated])
        by (metis fst_conv setr.cases swap_simps(3))
      done
    subgoal for \<Gamma>' t T' _ u
      by auto
    subgoal for \<Gamma>' X T1 t T2
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FVars_typ T1  \<union> FVars_typ T2 \<union> FTVars t \<union> FFVars_ctxt \<Gamma> \<union> Inl -` dom \<Gamma>"]])
       apply (auto simp: insert_bound_UNIV infinite_UNIV intro!: typ.Un_bound typ.UN_bound typ.set_bd_UNIV trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inl lfset.UNIV_cinfinite)
      subgoal for Y
        apply (rule exI[of _ "{Y}"]; simp add: TAbs_inject)
        apply (rule conjI)
        apply (metis imageI setl.cases)
        apply (rule exI[of _ "permute_typ (X \<leftrightarrow> Y) T2"])
        apply (frule prems(1)[THEN typing_fresh_ty_extend])
        apply (drule prems(2)[of "X \<leftrightarrow> Y" id, rotated -1])
            apply (auto simp add: typ_inject id_on_def dom_def subset_eq image_iff
            intro!: list.map_ident_strong sum.map_ident_strong typ.permute_cong_id exI[of _ "X \<leftrightarrow> Y"]
            elim!: arg_cong2[where f = "\<lambda>x y. R x y _", THEN iffD1, rotated 2])
          apply (metis swap_def)
         apply (metis fst_conv setl.cases swap_def)
        by (metis snd_conv swap_def)
      done
    subgoal for \<Gamma>' t X T11 T12 T2
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FVars_typ T11  \<union> FVars_typ T12  \<union> FVars_typ T2 \<union> FTVars t \<union> FFVars_ctxt \<Gamma> \<union> Inl -` dom \<Gamma>"]])
       apply (auto simp: insert_bound_UNIV infinite_UNIV intro!: typ.Un_bound typ.UN_bound typ.set_bd_UNIV trm.set_bd_UNIV) []
      apply (meson finite_set cinfinite_imp_infinite finite_imageI finite_ordLess_infinite2 finite_vimageI inj_Inl lfset.UNIV_cinfinite)
      subgoal for Y
        apply (rule exI[of _ "{Y}"]; simp add: TAbs_inject)
        apply (intro conjI)
          apply (metis imageI setl.cases)
         apply (subst FVars_tvsubst_typ)
        apply simp
         apply auto []
        apply (rule exI[of _ "T11"])
        apply (rule exI[of _ "permute_typ (X \<leftrightarrow> Y) T12"])
        apply (frule prems(1))
            apply auto
         apply (rule Forall_eq_tvsubst_typ)
         apply (simp add: typ_inject)
         apply (rule exI[of _ "X \<leftrightarrow> Y"]; simp add: id_on_def)
         apply (simp add: swap_def)
        by (metis typ.inject(3))
      done
    subgoal
      apply (rule disjI2)
      apply force
      done
    subgoal
      apply (rule disjI2)
      apply force
      done
    subgoal
      apply (rule disjI2)
      apply force
      done
    subgoal for \<Gamma>' t T' p \<Delta> u U
      apply (rule disjI2)+
      apply (rule mp[OF _ extend_fresh[where B="PVars p" and A="Inr -` dom \<Gamma> \<union> FVars t \<union> FVars u"]])
      apply (rule impI)
         apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (rule exI[of _ "{}"]; simp)
        apply (rule exI[of _ "\<sigma> ` PVars p"]; simp)
        apply (rule conjI)
        subgoal
         apply (simp add: id_on_def image_Un Int_Un_distrib Int_Un_distrib2 image_iff vimage_def) []
          apply auto
          apply (metis (no_types, lifting) Int_emptyD fst_conv image_eqI setr.cases)
          done
        apply (rule exI[of _ t])
        apply (rule exI[of _ T'])
        apply (rule exI[of _ "vvsubst_pat id \<sigma> p"])
        apply (rule conjI)
        apply (simp add: pat.set_map)
        apply (rule exI[of _ "map (map_prod (map_sum id \<sigma>) id) \<Delta>"])
        apply (rule exI[of _ "permute_trm id \<sigma> u"])
        apply (intro conjI)
        subgoal
          apply (rule exI[of _ "\<sigma>"]; simp)
          apply (auto simp: id_on_def)
          done
          apply assumption
        subgoal
          apply (drule pat_typing_equiv[of id \<sigma>, rotated 4])
          apply auto
          done
        subgoal
          apply (frule prems(1)[THEN typing_wf_ctxt[of "\<Gamma> \<^bold>, \<Delta>"]])
          apply (drule prems(2)[of id \<sigma> "\<Gamma> \<^bold>, \<Delta>", rotated 4])
              apply auto [4]
          apply (subgoal_tac "map (map_prod (map_sum id \<sigma>) id) \<Gamma> = \<Gamma>")
           apply simp
          apply (auto intro!: list.map_ident_strong sum.map_ident_strong)
          subgoal for z U x
            apply (cases "x \<in> PVars p")
            subgoal
              apply (cases z; auto)
              apply (drule pat_typing_dom)
              apply (drule wf_ctxt_concat_disjoint)
              apply auto
              done
            apply (metis (mono_tags, lifting) Diff_iff Un_iff fst_conv id_on_def imageI setr.cases
                vimage_eq)
            done
          done
        done
      apply (auto intro!: typ.Un_bound simp: finite_vimageI pat.set_bd_UNIV trm.set_bd_UNIV infinite_UNIV card_of_minus_bound)
      done
    done
  done

inductive match for \<sigma> where
  MPVar: "\<sigma> X = v \<Longrightarrow> match \<sigma> (PVar X T) v"
| MPRec: "nonrep_PRec PP \<Longrightarrow> labels PP \<subseteq> labels VV \<Longrightarrow>
    (\<And>l P v. (l, P) \<in>\<in> PP \<Longrightarrow> (l, v) \<in>\<in> VV \<Longrightarrow> match \<sigma> P v) \<Longrightarrow> match \<sigma> (PRec PP) (Rec VV)"

definition "restrict \<sigma> A v x = (if x \<in> A then \<sigma> x else v x)"
       
lemma match_cong: "match \<sigma> p v \<Longrightarrow> (\<forall>x \<in> PVars p. \<sigma> x = \<tau> x) \<Longrightarrow> match \<tau> p v"
  by (induct p v rule: match.induct)
    (force simp: restrict_def values_lfin_iff Ball_def Bex_def intro!: match.intros)+

lemma match_restrict: "match \<sigma> p v \<Longrightarrow> match (restrict \<sigma> (PVars p) Var) p v"
  by (erule match_cong) (auto simp: restrict_def)

inductive step where
  AppAbs: "value v \<Longrightarrow> step (App (Abs x T t) v) (tvsubst (Var(x := v)) TyVar t)"
| TAppTAbs: "step (TApp (TAbs X T t) T2) (tvsubst Var (TyVar(X := T2)) t)"
| LetV: "value v \<Longrightarrow> match \<sigma> p v \<Longrightarrow> step (Let p v u) (tvsubst (restrict \<sigma> (PVars p) Var) TyVar u)"
| ProjRec: "\<forall>v \<in> values VV. value v \<Longrightarrow> (l, v) \<in>\<in> VV \<Longrightarrow> step (Proj (Rec VV) l) v"
| AppCong1: "step t t' \<Longrightarrow> step (App t u) (App t' u)"
| AppCong2: "value v \<Longrightarrow> step t t' \<Longrightarrow> step (App v t) (App v t')"
| TAppCong: "step t t' \<Longrightarrow> step (TApp t T) (TApp t' T)"
| ProjCong: "step t t' \<Longrightarrow> step (Proj t l) (Proj t' l)"
| RecCong: "step t t' \<Longrightarrow> (l, t) \<in>\<in> XX \<Longrightarrow> step (Rec XX) (Rec (XX\<lbrace>l := t'\<rbrace>))"
| LetCong: "step t t' \<Longrightarrow> step (Let p t u) (Let p t' u)"

lemma proj_ctxt_empty[simp]: "proj_ctxt \<emptyset> = \<emptyset>"
  unfolding proj_ctxt_def map_filter_def
  by auto

lemma canonical_closed_Fun[OF _ refl refl]: "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> T = T11 \<rightarrow> T12 \<Longrightarrow> value v \<Longrightarrow> \<exists>x S11 t. v = Abs x S11 t"
  by (induction \<Gamma> v T arbitrary: T11 T12 rule: typing.induct) (auto elim: value.cases ty.cases)

lemma canonical_closed_Forall[OF _ refl refl]: "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> T = Forall X T11 T12 \<Longrightarrow> value v \<Longrightarrow> \<exists>X S11 t. v = TAbs X S11 t"
  by (induction \<Gamma> v T arbitrary: X T11 T12 rule: typing.induct) (auto elim: value.cases ty.cases)

lemma canonical_closed_TRec[OF _ refl refl]: "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> T = TRec TT \<Longrightarrow> value v \<Longrightarrow> \<exists>XX. v = Rec XX \<and> labels TT \<subseteq> labels XX \<and> (\<forall>v \<in> values XX. value v)"
  apply (induction \<Gamma> v T arbitrary: TT rule: typing.induct)
          apply (auto simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id] lfset.set_map elim: value.cases ty.cases)
   apply (smt (verit) SA_TRecER order.trans empty_iff list.set(1))
  apply (metis (no_types, opaque_lifting) fstI lfin_map_lfset trm.distinct(37,39) trm.inject(6)
      value.cases values_lfin_iff)
  done

lemma TRec_typingD[OF _ refl]: "\<Gamma> \<^bold>\<turnstile> Rec XX \<^bold>: TRec TT \<Longrightarrow> \<Gamma> = \<emptyset> \<Longrightarrow> (l, v) \<in>\<in> XX \<Longrightarrow> (l, T) \<in>\<in> TT \<Longrightarrow> \<emptyset> \<^bold>\<turnstile> v \<^bold>: T"
  apply (induction \<Gamma> "Rec XX" "TRec TT" arbitrary: XX TT T rule: typing.induct)
apply (auto simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id] lfset.set_map elim: value.cases ty.cases)
   apply (erule SA_TRecER; auto)
   apply (drule meta_spec2, drule meta_mp, assumption)
  apply (erule exE conjE)+
   apply ((drule meta_spec)+, drule meta_mp, rule refl, drule meta_mp, rule refl, drule meta_mp, assumption)
   apply (drule meta_mp, assumption)
   apply (drule meta_mp, assumption)
   apply (erule TSub)
   apply simp
  apply (auto simp: lfin_map_lfset)
  by (metis (no_types, lifting) fst_conv lfin_label_inject prod_in_Collect_iff subset_eq values_lfin_iff)

lemma match_unique_on_PVars: "match \<sigma> P v \<Longrightarrow> match \<sigma>' P v \<Longrightarrow> x \<in> PVars P \<Longrightarrow> \<sigma> x = \<sigma>' x"
  apply (induct P v rule: match.induct)
   apply simp_all
   apply (erule match.cases; auto simp: PVar_def PRec_def Rep_pat[simplified] lfin_map_lfset dest!: Abs_pat_inject[simplified, THEN iffD1, rotated 2] split: if_splits)
   apply (erule match.cases; auto simp: PVar_def PRec_def Rep_pat[simplified] lfin_map_lfset nonrep_PRec_alt dest!: Abs_pat_inject[simplified, THEN iffD1, rotated 2] split: if_splits)
  apply (smt (verit, ccfv_threshold) Rep_pat_inverse labels_lfin_iff lfin_map_lfset subset_eq values_lfin_iff)
  done

lemma pat_typing_ex_match:
  fixes p :: "('tv::var, 't::var) pat" and v :: "('tv::var, 't::var) trm"
  shows "\<turnstile> p : T \<rightarrow> \<Delta> \<Longrightarrow> \<emptyset> \<^bold>\<turnstile> v \<^bold>: T \<Longrightarrow> value v \<Longrightarrow> \<exists>\<sigma>. match \<sigma> p v"
proof (induct p T \<Delta> arbitrary: v rule: pat_typing.induct)
  case (PRec PP TT \<Delta> xs)
  from canonical_closed_TRec[OF PRec(6,7)]
  obtain XX where XX: "v = Rec XX" "labels TT \<subseteq> labels XX" "\<forall>v\<in>values XX. value v"
    by blast
  define \<sigma> where "\<sigma> = (\<lambda>x. if \<exists>l P. (l, P) \<in>\<in> PP \<and> x \<in> PVars P then
    (SOME \<sigma>. match \<sigma> (lflookup PP (lfrlookup PP (\<lambda>P. x \<in> PVars P))) (lflookup XX (lfrlookup PP (\<lambda>P. x \<in> PVars P)))) x else Var x)"
  show ?case
    unfolding XX
    apply (rule exI[of _ \<sigma>])
    apply (rule MPRec[OF PRec(1) ord_eq_le_trans[OF PRec(2) XX(2)]])
    subgoal for l P v'
    apply (frule PRec(4)[of _ _ _ v'])
       apply (rule lflookup_lfin)
    using PRec(2) labels_lfin_iff apply blast
      apply (rule TRec_typingD)
        apply (rule PRec(6)[unfolded XX])
       apply assumption
      apply (rule lflookup_lfin)
    using PRec(2) labels_lfin_iff apply blast
     apply (simp add: XX(3) lfin_values)
    apply (erule exE)
    apply (rule match_cong)
    apply assumption
    apply (rule ballI)
    apply (unfold \<sigma>_def)
    apply (subst if_P)
     apply blast
    subgoal for \<sigma> x
      apply (subgoal_tac "lfrlookup PP (\<lambda>P. x \<in> PVars P) = l")
      apply (simp add: lflookup_eq)
    apply (rule match_unique_on_PVars)
         apply assumption
        apply (metis tfl_some)
      apply assumption
      apply (rule lfrlookup_eq)
        apply assumption
      apply assumption
      apply (metis Int_emptyD PRec(1) lflookup_eq nonrep_PRec_def)
      done
    done
  done
qed (meson MPVar)

lemma progress[OF _ refl]: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<Gamma> = [] \<Longrightarrow> value t \<or> (\<exists>t'. step t t')"
  apply (induction \<Gamma> t T rule: typing.induct)
          apply (auto 0 2
     simp: subset_eq labels_lfin_iff Ball_def lfset.set_map lfset.in_rel[of id, simplified, unfolded lfset.map_id]
     intro!: value.intros intro: step.intros elim!: value.cases
     dest!: canonical_closed_Fun canonical_closed_Forall canonical_closed_TRec)
  apply (metis RecCong fstI lfin_map_lfset values_lfin_iff)
     apply (meson ProjRec)
    apply (drule (1) pat_typing_ex_match; auto intro!: value.intros intro: step.intros)+
  done

lemma set_proj_ctxt_eq: "set \<Gamma> = set \<Delta> \<Longrightarrow> set (proj_ctxt \<Gamma>) = set (proj_ctxt \<Delta>)"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma wf_ctxt_extend_permute: "\<turnstile> \<Gamma> \<^bold>, \<Gamma>' OK \<Longrightarrow> set \<Gamma> = set \<Delta> \<Longrightarrow> \<turnstile> \<Delta> OK \<Longrightarrow> \<turnstile> \<Delta> \<^bold>, \<Gamma>' OK"
  by (induct \<Gamma>') auto

lemma typing_permute: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Delta> OK \<Longrightarrow> set \<Gamma> = set \<Delta> \<Longrightarrow> \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
  apply (binder_induction \<Gamma> t T arbitrary: \<Delta> avoiding: \<Gamma> t T \<Delta> rule: typing.strong_induct)
          apply (simp_all add: TVar)
         apply (metis TAbs list.simps(15) typing_wf_ctxt wf_ctxt_Cons wf_ctxt_ConsE)
        apply (metis TApp)
       apply (metis TTAbs list.simps(15) typing_wf_ctxt wf_ctxt_Cons wf_ctxt_ConsE)
      apply (metis TTApp set_proj_ctxt_eq ty_permute wf_ty_proj_ctxt)
     apply (metis TSub set_proj_ctxt_eq ty_permute typing_wf_ty)
    apply (simp add: TRec lfset.rel_mono_strong)
   apply (metis TProj)
  apply (metis TLet set_append typing_wf_ctxt wf_ctxt_extend_permute)
  done

lemma proj_ctxt_concat[simp]: "proj_ctxt (\<Gamma> \<^bold>, \<Delta>) = proj_ctxt \<Gamma> \<^bold>, proj_ctxt \<Delta>"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma proj_ctxt_extend_Inl[simp]: "proj_ctxt (\<Gamma> \<^bold>, Inl x <: U) = proj_ctxt \<Gamma> \<^bold>, x <: U"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma proj_ctxt_extend_Inr[simp]: "proj_ctxt (\<Gamma> \<^bold>, Inr x <: U) = proj_ctxt \<Gamma>"
  by (auto simp: proj_ctxt_def map_filter_def)

lemma dom_proj_ctxt: "dom (proj_ctxt \<Gamma>) = Inl -` dom \<Gamma>"
proof (induct \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case
    by (cases a; cases "fst a") auto
qed simp

lemma set_proj_ctxt: "set (proj_ctxt \<Gamma>) = {(x, T). (Inl x, T) \<in> set \<Gamma>}"
  by (force simp: proj_ctxt_def map_filter_def image_iff split: sum.splits prod.splits)

lemma wf_ctxt_insert_middle:
  "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> x \<notin> dom \<Gamma> \<Longrightarrow> x \<notin> dom \<Delta> \<Longrightarrow> U closed_in proj_ctxt \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, \<Delta> OK"
  by (induct \<Delta>) (auto simp: dom_proj_ctxt)

lemma typing_weaken1: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, x <: U OK \<Longrightarrow> \<Gamma> \<^bold>, x <: U \<^bold>\<turnstile> t \<^bold>: T"
proof (binder_induction \<Gamma> t T avoiding: \<Gamma> t T x U rule: typing.strong_induct)
  case (TAbs \<Gamma> z T1 u T2)
  then have "\<turnstile> \<Gamma> \<^bold>, Inr z <: T1 \<^bold>, x <: U OK" "\<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, Inr z <: T1 OK"
    by (cases x; auto dest!: typing_wf_ctxt)+
  with TAbs show ?case
    by (intro typing.TAbs) (auto elim: typing_permute)
next
  case (TTApp \<Gamma> t1 X T11 T12 T2)
  then show ?case
  proof (cases x)
    case (Inl a)
    with TTApp show ?thesis
      by (smt (verit) proj_ctxt_extend_Inl ty_weakening_extend typing.simps typing_wf_ty wf_ConsE)
  qed (auto intro: typing.TTApp)
next
  case (TTAbs \<Gamma> X T1 t T2)
  then have "\<turnstile> \<Gamma> \<^bold>, Inl X <: T1 \<^bold>, x <: U OK" "\<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, Inl X <: T1 OK"
    by (cases x; auto dest!: typing_wf_ctxt)+
  with TTAbs show ?case
    by (intro typing.TTAbs) (auto elim: typing_permute)
next
  case (TSub \<Gamma> t S T)
  then show ?case
  proof (cases x)
    case (Inl a)
    with TSub show ?thesis
      by (smt (verit) proj_ctxt_extend_Inl ty_weakening_extend typing.simps typing_wf_ty wf_ConsE)
  qed (auto intro: typing.TSub)
next
  case (TRec \<Gamma> XX TT)
  then show ?case
    by (auto intro!: typing.TRec elim: lfset.rel_mono_strong)
next
  case (TLet \<Gamma> t T p \<Delta> u U')
  then have "\<turnstile> \<Gamma> \<^bold>, \<Delta> \<^bold>, x <: U OK"
     apply (auto simp add: image_Un Domain.DomainI fst_eq_Domain dest!: typing_wf_ctxt pat_typing_dom)
    apply (metis Domain.DomainI Int_emptyD image_iff singletonI sum_set_simps(4))
    done
  moreover from TLet have "\<turnstile> \<Gamma> \<^bold>, x <: U \<^bold>, \<Delta> OK"
    apply (auto simp add: image_Un Domain.DomainI fst_eq_Domain dest!: typing_wf_ctxt pat_typing_dom)
    apply (erule wf_ctxt_insert_middle)
      apply (auto simp: wf_ctxt_insert_middle)
    apply (metis Domain.DomainI Int_emptyD image_iff singletonI sum_set_simps(4))
    apply (metis Un_iff dom_proj_ctxt fst_eq_Domain sup.orderE)
    done
  ultimately show ?case using TLet
    by (auto intro!: typing.TLet elim: typing_permute)
qed (auto intro: typing.intros)

lemma typing_weaken: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> \<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
proof (induct \<Delta>)
  case (Cons xT \<Delta>)
  then show ?case
    by (auto simp: typing_weaken1 wf_ctxt_Cons)
qed simp

lemma typing_narrowing: "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Gamma> \<^bold>, Inl X <: P \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T"
proof (binder_induction "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>" t T arbitrary: \<Delta> avoiding: X \<Gamma> \<Delta> P Q t T rule: typing.strong_induct)
  case (TVar x T \<Delta>)
  from TVar(1,3) have "\<turnstile> \<Gamma> \<^bold>, Inl X <: P \<^bold>, \<Delta> OK"
    apply (induct \<Delta>)
     apply (auto simp: image_Un rev_image_eqI dest!: well_scoped(1))
    apply (metis (no_types, opaque_lifting) Pair_inject proj_ctxt_extend_Inl subset_eq wf_ConsE wf_ctxt_Cons wf_ty_proj_ctxt)
    done
  with TVar show ?case
    by (auto intro: typing.TVar)
next
  case (TRec \<Gamma>' XX \<Delta>)
  from TRec(1,3) have "\<turnstile> \<Gamma> \<^bold>, Inl X <: P \<^bold>, \<Delta> OK"
    apply (induct \<Delta>)
     apply (auto simp: image_Un rev_image_eqI dest!: well_scoped(1))
    apply (metis (no_types, opaque_lifting) Pair_inject proj_ctxt_extend_Inl subset_eq wf_ConsE wf_ctxt_Cons wf_ty_proj_ctxt)
    done
  with TRec show ?case
    by (auto simp: ty_narrowing2 elim!: lfset.rel_mono_strong intro!: typing.TRec)
qed (auto simp flip: append_Cons simp: ty_narrowing2 intro: typing.intros)

lemma wf_ctxt_weaken: "\<turnstile> \<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta> OK \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, \<Delta> OK"
  by (induct \<Delta>) auto
lemma wf_ctxt_notin: "\<turnstile> \<Gamma> \<^bold>, x <: Q \<^bold>, \<Delta> OK \<Longrightarrow> x \<notin> dom \<Gamma> \<and> x \<notin> dom \<Delta>"
  by (induct \<Delta>) auto

thm trm.subst

lemma typing_tvsubst: "\<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> q \<^bold>: Q \<Longrightarrow> \<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> tvsubst (Var(x := q)) TyVar t \<^bold>: T"
proof (binder_induction "\<Gamma> \<^bold>, Inr x <: Q \<^bold>, \<Delta>" t T arbitrary: \<Gamma> \<Delta> avoiding: \<Gamma> \<Delta> x q Q t T rule: typing.strong_induct)
  case (TVar y T \<Gamma> \<Delta>)
  then have "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK" "Inr x \<notin> dom \<Gamma>" "Inr x \<notin> dom \<Delta>"
    by (auto dest: wf_ctxt_weaken wf_ctxt_notin)
  with TVar show ?case
    by (auto simp add: image_iff intro!: typing.TVar elim: typing_weaken)
next
  case (TAbs x T1 t T2 \<Gamma> \<Delta>)
  then show ?case
    by (subst trm.subst)
      (auto simp flip: append_Cons dest!: set_mp[OF SSupp_fun_upd_subset] IImsupp_fun_upd_subset[THEN set_mp] intro!: typing.TAbs)
next
  case (TApp t1 T11 T12 t2 \<Gamma> \<Delta>)
  then show ?case
    by (auto simp: cmin_greater intro!: typing.TApp)
next
  case (TTAbs X T1 t T2 \<Gamma> \<Delta>)
  then show ?case
    by (subst trm.subst) (auto dest!: IImsupp_fun_upd_subset[THEN set_mp] simp flip: append_Cons intro!: typing.TTAbs)
next
  case (TTApp t1 X T11 T12 T2 \<Gamma> \<Delta>)
  then show ?case
    by (auto simp: cmin_greater intro!: typing.TTApp)
next
  case (TSub t S T \<Gamma> \<Delta>)
  then show ?case
    by (fastforce intro: typing.TSub)
next
  case (TRec XX TT \<Gamma> \<Delta>)
  then show ?case
    by (auto simp: wf_ctxt_weaken lfset.rel_map elim!: lfset.rel_mono_strong intro!: typing.TRec)
next
  case (TProj ta TT l Ta \<Gamma> \<Delta>)
  then show ?case
    by (auto intro!: typing.TProj)
next
  case (TLet t T p \<Delta>' u U \<Gamma> \<Delta>)
  then show ?case
    by (subst trm.subst)
      (auto simp: vvsubst_pat_tvsubst_pat[of id id, simplified, symmetric]
          simp flip: append_assoc intro!: typing.TLet dest!: set_mp[OF SSupp_fun_upd_subset] IImsupp_fun_upd_subset[THEN set_mp])
qed

lemma Abs_inject_permute: "x \<notin> FVars u \<Longrightarrow> Abs x T t = Abs y U u \<longleftrightarrow> (T = U \<and> t = permute_trm id (x \<leftrightarrow> y) u)"
  apply (auto simp: Abs_inject trm.permute_comp supp_comp_bound infinite_UNIV bij_implies_inject id_on_def
     trm.FVars_permute
     intro!: trm.permute_cong_id[symmetric] trm.permute_cong_id exI[of _ "x \<leftrightarrow> y"])
  by (metis swap_def)

lemma TAbs_inject_permute: "X \<notin> FTVars u \<Longrightarrow> TAbs X T t = TAbs Y U u \<longleftrightarrow> (T = U \<and> t = permute_trm (X \<leftrightarrow> Y) id u)"
  apply (auto simp: TAbs_inject trm.permute_comp supp_comp_bound infinite_UNIV bij_implies_inject id_on_def
     trm.FVars_permute
     intro!: trm.permute_cong_id[symmetric] trm.permute_cong_id exI[of _ "X \<leftrightarrow> Y"])
  by (metis swap_def)

lemma typing_AbsD: "\<Gamma> \<^bold>\<turnstile> Abs x S1 s2 \<^bold>: T \<Longrightarrow> x \<notin> Inr -` dom \<Gamma> \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> T <: U1 \<rightarrow> U2 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> U1 <: S1 \<and>
   (\<exists>S2. (\<Gamma> \<^bold>, Inr x <: S1 \<^bold>\<turnstile> s2 \<^bold>: S2) \<and> (proj_ctxt \<Gamma> \<turnstile> S2 <: U2))"
proof (binder_induction \<Gamma> "Abs x S1 s2" T avoiding: \<Gamma> x S1 s2 T U1 U2 rule: typing.strong_induct)
  case (TAbs \<Gamma> y T1 t' T2)
  from TAbs(1-4,6-) show ?case
    apply (auto simp: Abs_inject_permute elim!: SA_ArrEL intro!: exI[of _ T2])
    apply (frule typing.equiv[of id "y \<leftrightarrow> x", rotated 4])
        apply (auto 0 4 simp: trm.permute_comp supp_comp_bound infinite_UNIV setr.simps Domain.DomainI fst_eq_Domain
          intro!: list.map_ident_strong sum.map_ident_strong trm.permute_cong_id
          elim!: arg_cong2[where f="\<lambda>\<Gamma> t. \<Gamma> \<^bold>, Inr x <: S1 \<^bold>\<turnstile> t \<^bold>: T2", THEN iffD1, rotated 2])
    by (metis Domain.DomainI fst_conv swap_def)
next
  case (TSub \<Gamma> S T)
  then show ?case
    using ty_transitivity2 by blast
qed auto

lemma typing_TAbsD: "\<Gamma> \<^bold>\<turnstile> TAbs X S1 s2 \<^bold>: T \<Longrightarrow> X \<notin> Inl -` dom \<Gamma> \<Longrightarrow> X \<notin> FFVars_ctxt \<Gamma> \<Longrightarrow> X \<notin> FVars_typ U1 \<Longrightarrow>
   proj_ctxt \<Gamma> \<turnstile> T <: \<forall>X <: U1. U2 \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> U1 <: S1 \<and>
   (\<exists>S2. (\<Gamma> \<^bold>, Inl X <: U1 \<^bold>\<turnstile> s2 \<^bold>: S2) \<and> (proj_ctxt \<Gamma> \<^bold>, X <: U1 \<turnstile> S2 <: U2))"
proof (binder_induction \<Gamma> "TAbs X S1 s2" T avoiding: \<Gamma> X S1 s2 T U1 U2 rule: typing.strong_induct)
  case (TTAbs \<Gamma> Y T1 t' T2)
  have 1[simp]: "permute_typ (X \<leftrightarrow> Y) S1 = S1"
    by (metis (no_types, lifting) TTAbs.hyps(11,12,4,9) rrename_swap_FFvars snd_conv subsetD trm.inject(4) typing_wf_ctxt wf_ctxt_ConsE)
  have 2[simp]: "map (map_prod (map_sum (X \<leftrightarrow> Y) id) (permute_typ (X \<leftrightarrow> Y))) \<Gamma> = \<Gamma>"
    apply (auto intro!: list.map_ident_strong sum.map_ident_strong typ.permute_cong_id)
     apply (metis TTAbs.hyps(1,12) UN_I fst_eqD imageI setl.simps swap_simps(3) vimageI)
    by (metis TTAbs.hyps(13,2) UN_I image_eqI snd_conv swap_def)
  have 3[simp]: "FVars_typ T2 \<subseteq> dom (proj_ctxt \<Gamma>) \<union> {Y}"
    by (metis Diff_subset_conv TTAbs.hyps(15) le_sup_iff sup_commute typ.set(4) well_scoped(1))
  have 4[simp]: "X \<notin> dom (proj_ctxt \<Gamma>)"
    by (metis TTAbs.hyps(12) dom_proj_ctxt)

  from TTAbs(1-9,11-) show ?case
    apply (auto simp: TAbs_inject_permute)
     apply (auto simp add: typ_inject elim!: SA_AllEL) []
    apply (frule typing.equiv[of "X \<leftrightarrow> Y" id, rotated 4])
    apply (auto simp: trm.permute_comp supp_comp_bound infinite_UNIV setr.simps Domain.DomainI fst_eq_Domain
          trm.permute_id) [5]
    apply (erule SA_AllER)
     apply simp
    apply (drule Forall_swapD)+
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (rule exI)
     apply (simp add: swap_sym)
    apply (rule conjI)
     apply (rule typing_narrowing[where \<Delta>="[]", simplified])
       apply assumption
      apply assumption
    subgoal for S1 Z S2
      apply (frule wf_context[where \<Gamma> = "_ \<^bold>, Z <: U1"])
      apply (frule ty.equiv[of "X \<leftrightarrow> Z" "_ \<^bold>, Z <: U1", rotated 2])
        apply (auto split: if_splits simp: typ.permute_comp)
      apply (subgoal_tac "permute_typ (X \<leftrightarrow> Z) U1 = U1")
      apply (subgoal_tac "map (map_prod (X \<leftrightarrow> Z) (permute_typ (X \<leftrightarrow> Z))) (proj_ctxt \<Gamma>) = proj_ctxt \<Gamma>")
      apply (subgoal_tac "permute_typ (X \<leftrightarrow> Z \<circ> Z \<leftrightarrow> Y) T2 = permute_typ (X \<leftrightarrow> Y) T2")
apply (auto intro!: typ.permute_cong list.map_ident_strong sum.map_ident_strong typ.permute_cong_id
           simp: supp_comp_bound infinite_UNIV)
      apply (metis (no_types, lifting) "3" TTAbs.hyps(12) Un_empty_right Un_insert_right dom_proj_ctxt in_mono insertE swap_def)
        apply (metis Domain.DomainI TTAbs.hyps(12) dom_proj_ctxt fst_eq_Domain swap_def)
       apply (metis (no_types, opaque_lifting) "4" UN_I image_eqI split_pairs2 swap_simps(3) wf_FFVars)
      by (metis swap_def ty_fresh_extend)
    done
next
  case (TSub \<Gamma> S T)
  then show ?case
    using ty_transitivity2 by fast
qed auto

lemma typing_RecD: "\<Gamma> \<^bold>\<turnstile> Rec VV \<^bold>: S \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> S <: TRec TT \<Longrightarrow> labels TT \<subseteq> labels VV \<and>
   (\<forall>l v T. (l, v) \<in>\<in> VV \<longrightarrow> (l, T) \<in>\<in> TT \<longrightarrow> \<Gamma> \<^bold>\<turnstile> v \<^bold>: T)"
proof (binder_induction \<Gamma> "Rec VV" S avoiding: \<Gamma> S rule: typing.strong_induct)
  case (TRec \<Gamma>' XX TTa)
  then show ?case
    apply (auto simp: simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id]
      lfin_map_lfset lfset.set_map values_lfin_iff subset_eq Ball_def)
     apply (metis SA_TRecER in_mono labelist_map_lfset set_labelist typ.distinct(17) typ.inject(4))
    apply (metis SA_TRecER[of "proj_ctxt \<Gamma>'" "TRec TTa" TT] TSub[of \<Gamma>'] lfin_label_inject[of _ _ TTa]
        lfin_map_lfset[of _ "snd (_, _)" snd] snd_conv typ.distinct(17)[of TTa] typ.inject(4)[of TTa])
    done
next
  case (TSub \<Gamma> S T)
  then show ?case
    using ty_transitivity2 by blast
qed auto

lemma typing_well_scoped: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> T closed_in proj_ctxt \<Gamma>"
proof (binder_induction \<Gamma> t T avoiding: \<Gamma> T t rule: typing.strong_induct)
  case (TVar \<Gamma> x T)
  then show ?case
    by (induct \<Gamma>) (auto simp: dom_proj_ctxt)
next
  case (TAbs \<Gamma> x T1 t T2)
  then show ?case
    apply (auto simp: dom_proj_ctxt)
    by (smt (verit, ccfv_SIG) in_mono prod.inject typing_wf_ctxt vimage_eq wf_ctxt_ConsE)
next
  case (TTAbs \<Gamma> X T1 t T2)
  then show ?case
    apply (auto simp: dom_proj_ctxt)
    by (smt (verit, ccfv_SIG) in_mono prod.inject typing_wf_ctxt vimage_eq wf_ctxt_ConsE)
next
  case (TTApp \<Gamma> t1 X T11 T12 T2)
  then show ?case
    apply (auto simp: dom_proj_ctxt)
    apply (subst (asm) (1 2) FVars_tvsubst_typ)
    apply (auto split: if_splits)
    apply (drule well_scoped(1))
    apply (auto simp: dom_proj_ctxt)
    done
next
  case TSub
  then show ?case
    using well_scoped(2) by blast
next
  case (TRec \<Gamma>' XX TT)
  then show ?case
    by (force simp: dom_proj_ctxt lfset.set_map lfset.in_rel[of id, simplified, unfolded lfset.map_id])
next
  case (TProj \<Gamma>' t TT l Ta)
  then show ?case
    by (force simp: dom_proj_ctxt values_lfin_iff)
next
  case (TLet \<Gamma>' t Ta p \<Delta> u U)
  then show ?case
    by (auto simp: dom_proj_ctxt image_Un subset_eq dest!: pat_typing_dom)
qed auto

lemma ty_refl': "\<lbrakk> \<turnstile> \<Gamma> ok ; T closed_in \<Gamma>; T = U \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> T <: U"
  using ty_refl by blast

lemma finite_FVars[simp]: "finite (FVars t)"
  by (induct t) auto
lemma finite_FTVars[simp]: "finite (FTVars t)"
  by (induct t) auto

lemmas tvsubst_pat_id[simp] = pat.Sb_Inj

lemma SSupp_restrict: "SSupp TyVar (restrict f A TyVar) \<subseteq> SSupp TyVar f"
  unfolding restrict_def
  by (simp add: Collect_mono_iff SSupp_def)
lemma SSupp_restrict_Var: "SSupp Var (restrict f A Var) \<subseteq> SSupp Var f"
  unfolding restrict_def
  by (simp add: Collect_mono SSupp_def)

lemmas [simp] = SSupp_restrict_Var[THEN card_of_subset_bound] SSupp_restrict[THEN card_of_subset_bound]

lemmas trm.inject(8)[simp del]
lemma permute_trm_eq_tvsubst':
  fixes \<sigma> :: "'v :: var \<Rightarrow> 'v" and \<tau> :: "'tv :: var \<Rightarrow> 'tv" and t :: "('tv :: var, 'v :: var) trm"
  assumes [simp]:
    "bij \<sigma>"
    "|supp \<sigma>| <o |UNIV::'v set|"
    "bij \<tau>"
    "|supp \<tau>| <o |UNIV::'tv set|"
  shows "permute_trm \<tau> \<sigma> t = tvsubst (restrict (Var o \<sigma>) (FVars t) Var) (restrict (TyVar o \<tau>) (FTVars t) TyVar) t"
proof -
  have [simp]: "|SSupp Var (restrict (Var o \<sigma>) (FVars t) Var)| <o |UNIV::'v set|"
    "|SSupp TyVar (restrict (TyVar o \<tau>) (FTVars t) TyVar)| <o |UNIV::'tv set|"
    by (auto simp: restrict_def SSupp_def infinite_UNIV)
  show ?thesis
    apply (binder_induction t avoiding: "supp \<sigma>" "supp \<tau>" t rule: trm.strong_induct)
          apply (auto simp: lfset.set_map intro!: lfset.map_cong0)
     apply (subst trm.subst)
              apply (auto simp: not_in_supp_alt bij_implies_inject[OF \<open>bij \<sigma>\<close>] restrict_def)
           apply (auto simp: IImsupp_def SSupp_def restrict_def)[1]
    apply (subst trm.subst)
         apply (auto simp: IImsupp_def not_in_supp_alt bij_implies_inject[OF \<open>bij \<tau>\<close>] trm.permute_id)
              apply (auto simp: SSupp_def IImsupp_def typ.vvsubst_permute[symmetric] typ.map_is_Sb restrict_def infinite_UNIV bij_implies_inject supp_def[symmetric] split: if_splits intro!: trm.Sb_cong lfset.map_cong)
    apply (subst trm.subst)
         apply (auto simp: IImsupp_def not_in_supp_alt bij_implies_inject[OF \<open>bij \<tau>\<close>] trm.permute_id)
              apply (auto simp: SSupp_def IImsupp_def typ.vvsubst_permute[symmetric] typ.map_is_Sb restrict_def infinite_UNIV bij_implies_inject supp_def[symmetric] split: if_splits intro!: trm.Sb_cong lfset.map_cong)
    apply (subst trm.subst)
         apply (auto simp: IImsupp_def not_in_supp_alt bij_implies_inject[OF \<open>bij \<tau>\<close>] trm.permute_id)
              apply (auto simp: SSupp_def IImsupp_def typ.vvsubst_permute[symmetric] typ.map_is_Sb restrict_def infinite_UNIV bij_implies_inject supp_def[symmetric] split: if_splits intro!: trm.Sb_cong lfset.map_cong)
    apply (metis DiffD2 Diff_triv assms(1) bij_implies_inject not_in_supp_alt)
     apply (metis DiffD2 Diff_triv assms(1) bij_implies_inject not_in_supp_alt)

    apply (subst pat.map_cong0[rotated -2])
            apply (rule refl)
           apply (erule id_onD[rotated])
           apply (simp add: Int_commute supp_id_on)
          apply (auto simp: id_def[symmetric] pat.map_is_Sb)
    apply (rule arg_cong3[of _ _ _ _ _ _ Let])
      apply (auto simp: pat.Sb_cong restrict_def)
     apply (rule trm.Sb_cong)
            apply (auto simp: IImsupp_def SSupp_def restrict_def pat.set_bd_UNIV)
        apply (metis (no_types, lifting) card_of_subset_bound mem_Collect_eq subsetI trm.set_bd_UNIV(1))
       apply (metis (no_types, lifting) card_of_subset_bound mem_Collect_eq subsetI trm.set_bd_UNIV(2))
    subgoal for x1 x2 x3
      apply (rule card_of_subset_bound[of _ "PTVars x1 \<union> FTVars x2 \<union> FTVars x3"])
       apply blast
      using pat.set_bd_UNIV trm.set_bd_UNIV infinite_class.Un_bound by meson
    subgoal for x1 x2 x3
      apply (rule card_of_subset_bound[of _ "FVars x2 \<union> FVars x3"])
       apply blast
      using pat.set_bd_UNIV trm.set_bd_UNIV infinite_class.Un_bound by meson
    apply (rule trm.Sb_cong)
            apply (auto simp: IImsupp_def SSupp_def restrict_def pat.set_bd_UNIV)
        apply (metis (no_types, lifting) card_of_subset_bound mem_Collect_eq subsetI trm.set_bd_UNIV(1))
       apply (metis (no_types, lifting) card_of_subset_bound mem_Collect_eq subsetI trm.set_bd_UNIV(2))
    subgoal for x1 x2 x3
      apply (rule card_of_subset_bound[of _ "PTVars x1 \<union> FTVars x2 \<union> FTVars x3"])
       apply blast
      using pat.set_bd_UNIV trm.set_bd_UNIV infinite_class.Un_bound by meson
    subgoal for x1 x2 x3
      apply (rule card_of_subset_bound[of _ "FVars x2 \<union> FVars x3"])
       apply blast
      using pat.set_bd_UNIV trm.set_bd_UNIV infinite_class.Un_bound by meson
    by (meson disjoint_iff_not_equal not_in_supp_alt)
qed

lemma SSupp_trm_restrict: "SSupp Var (restrict \<sigma> A Var) = SSupp Var \<sigma> \<inter> A"
  unfolding SSupp_def restrict_def
  by auto

lemma Int_bound2: "|B| <o r \<Longrightarrow> |A \<inter> B| <o r"
  using card_of_subset_bound inf_sup_ord(2) by blast

lemma SSupp_trm_restrict_bound[simp]:
  fixes \<sigma>::"'a::var \<Rightarrow> ('b::var, 'a) trm" and p::"('b, 'a) pat"
  shows "|SSupp Var (restrict \<sigma> (PVars p) Var)| <o |UNIV::'a set|"
  apply (subst SSupp_trm_restrict)
   apply (rule Int_bound2, rule pat.set_bd_UNIV)+
  done

lemma SSupp_typ_restrict[simp]: "SSupp TyVar (restrict \<sigma> A TyVar) = SSupp TyVar \<sigma> \<inter> A"
  unfolding SSupp_def restrict_def
  by auto

lemma FVars_restrict: "FVars (restrict \<sigma> A Var a) = (if a \<in> A then FVars (\<sigma> a) else {a})"
  by (auto simp: restrict_def)

lemma match_FVars: "match \<sigma> p v \<Longrightarrow> x \<in> PVars p \<Longrightarrow> FVars (\<sigma> x) \<subseteq> FVars v"
  by (induct p v rule: match.induct) (force simp: values_lfin_iff labels_lfin_iff Bex_def)+

lemma match_permute:
  "match \<sigma> (p :: ('tv::var, 'v::var) pat) v \<Longrightarrow> bij \<rho> \<Longrightarrow> |supp \<rho>| <o |UNIV :: 'v::var set| \<Longrightarrow> (\<forall>x. \<rho> (\<rho> x) = x) \<Longrightarrow>
   match (\<sigma> \<circ> \<rho>) (vvsubst_pat id \<rho> p) v"
  apply (induct p v rule: match.induct)
   apply (auto simp: id_def[symmetric] lfset.set_map lfin_map_lfset nonrep_PRec_def
     pat.set_map intro!: match.intros)
  by (metis Int_emptyD)

lemma nonrep_lfmap[simp]:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "nonrep_PRec (map_lfset id (vvsubst_pat f1 f2) PP) = nonrep_PRec PP"
proof -
  have 1: "bij (vvsubst_pat f1 f2)"
    apply (rule o_bij)
     apply (rule trans)
      apply (rule pat.map_comp0[symmetric])
           prefer 7
           apply (subst inv_o_simp1, rule assms)+
           apply (rule pat.map_id0)
          apply (rule assms supp_inv_bound bij_imp_bij_inv)+
    apply (rule trans)
      apply (rule pat.map_comp0[symmetric])
          apply (rule assms supp_inv_bound bij_imp_bij_inv)+
           apply (subst inv_o_simp2, rule assms)+
    apply (rule pat.map_id0)
    done
  then show ?thesis
    apply (unfold nonrep_PRec_def)
    apply (rule iffI)
     apply (rule allI impI)+
     apply (erule allE)+
     apply (erule impE)
      prefer 2
      apply (erule impE)
       apply (erule lfin_equiv[OF 1])
      apply (erule impE)
    apply (rotate_tac -1)
       apply (erule lfin_equiv[OF 1])
      apply (auto simp: pat.set_map assms)[2]
    apply (rule allI impI)+
    apply (erule allE)+
    apply (erule impE)
    apply assumption
     apply (erule impE)
      apply (rule equiv(14)[THEN iffD1, OF 1])
      apply (subst pat.map_comp[of "inv f1" "inv f2"])
           apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    using assms apply (unfold inv_o_simp2 pat.map_id)
    apply assumption
     apply (erule impE)
      apply (rule equiv(14)[THEN iffD1, OF 1])
      apply (subst pat.map_comp[of "inv f1" "inv f2"])
           apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    using assms apply (unfold inv_o_simp2 pat.map_id)
     apply assumption
    by (auto simp: pat.set_map supp_inv_bound)
qed

lemma restrict_equiv:
fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "permute_trm f1 f2 (restrict \<sigma> (PVars p) Var x) = restrict (permute_trm f1 f2 \<circ> \<sigma> \<circ> inv f2) (PVars (vvsubst_pat f1 f2 p)) Var (f2 x)"
  using assms by transfer (auto simp: restrict_def bij_implies_inject)
lemma match_equiv_aux:
fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "match \<sigma> p v \<Longrightarrow> match (permute_trm f1 f2 \<circ> \<sigma> \<circ> inv f2) (vvsubst_pat f1 f2 p) (permute_trm f1 f2 v)"
proof (induction rule: match.induct)
  case (MPVar X v T)
  then show ?case
    using assms by (auto intro: match.intros)
next
  case (MPRec PP VV)
  then show ?case
    using assms apply (auto simp: lfset.set_map intro!: match.intros)
    by (metis (no_types, lifting) lfin_map_lfset)
qed
lemma match_equiv:
fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "match (permute_trm f1 f2 \<circ> \<sigma> \<circ> inv f2) (vvsubst_pat f1 f2 p) (permute_trm f1 f2 v) = match \<sigma> p v"
  apply (rule iffI)
   apply (drule match_equiv_aux[of "inv f1" "inv f2", rotated -1])
  using assms apply (auto simp: supp_inv_bound comp_assoc[symmetric] trm.permute_comp0 trm.permute_id0 pat.map_comp trm.permute_comp)
   apply (auto simp: comp_assoc)[1]
  apply (erule match_equiv_aux)
     apply (rule assms)+
  apply assumption
  done

lemma Ball_value[equiv]:
fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "Ball (permute_trm f1 f2 ` values V) value = Ball (values V) value"
  using assms by (auto simp: equiv(26))
lemmas [equiv] = restrict_equiv[unfolded comp_def] match_equiv[unfolded comp_def] map_lfset_lfupdate

lemmas tvsubst_comp = trans[OF comp_apply[symmetric] trm.Sb_comp(1)[THEN fun_cong]]

lemma IImsupp_restrict_bound[intro!]: "(\<And>a. |Vrs a| <o |UNIV::'a::var set| ) \<Longrightarrow> |A| <o |UNIV::'a set| \<Longrightarrow> |IImsupp Inj Vrs (restrict \<sigma> A Inj)| <o |UNIV::'a set|"
  apply (auto simp: IImsupp_def restrict_def SSupp_def intro!: UN_bound)
  by (metis (no_types, lifting) card_of_subset_bound mem_Collect_eq subsetI)

lemma SSupp_restrict_bound[intro!]: "|A| <o |UNIV::'a set| \<Longrightarrow> |SSupp Inj (restrict \<sigma> A Inj)| <o |UNIV::'a set|"
  apply (auto simp: SSupp_def restrict_def)
  by (metis (no_types, lifting) card_of_subset_bound mem_Collect_eq subsetI)

lemmas [intro] = ordLeq_ordLess_trans[OF card_of_image]

lemma tvsubst_restrict[equiv]:
  fixes \<sigma>1::"'a::var \<Rightarrow> 'a" and \<sigma>2::"'b::var \<Rightarrow> 'b"
  assumes "bij \<sigma>1" "|supp \<sigma>1| <o |UNIV::'a set|" "bij \<sigma>2" "|supp \<sigma>2| <o |UNIV::'b set|"
    shows "permute_trm \<sigma>1 \<sigma>2 (tvsubst (restrict \<sigma>' (PVars p) Var) TyVar u) =
    tvsubst (restrict (\<lambda>a. permute_trm \<sigma>1 \<sigma>2 (\<sigma>' (inv \<sigma>2 a))) (\<sigma>2 ` PVars p) Var) TyVar (permute_trm \<sigma>1 \<sigma>2 u)"
  apply (rule trans)
  apply (rule trans[OF comp_apply[symmetric] trm.tvsubst_permute[THEN fun_cong]])
         apply (rule assms SSupp_Inj_bound)+
  using pat.set_bd_UNIV(2) trm.FVars_bd_UNIVs(1) apply blast
  using pat.set_bd_UNIV(2) apply blast
  apply (rule trans[OF comp_apply])
  apply (rule trm.Sb_cong)
  by (auto simp: assms supp_inv_bound pat.set_bd_UNIV trm.vvsubst_permute[symmetric]
            trm.IImsupp_natural restrict_def trm.set_map
          intro!: trm.SSupp_map_bound)

binder_inductive step
  subgoal premises prems for R B1 B2 t u
    unfolding ex_simps conj_disj_distribL ex_disj_distrib
    using prems(3)
    apply -
    apply (elim disjE conjE exE; hypsubst_thin)
    subgoal for v x T t
      apply (rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{x} \<union> FVars t \<union> FVars v"]])
      apply (metis lfset.Un_bound trm.set(9) trm.set_bd_UNIV(2))
      subgoal for y
        apply (rule exI[of _ "{}"])
        apply (rule conjI)
         apply simp
        apply (rule exI[of _ "{y}"])
        apply (rule conjI)
         apply (auto simp: trm.Vrs_Sb)
        apply (subst trm.vvsubst_permute[symmetric])
        apply auto[4]
        apply (subst trm.map_is_Sb)
          apply (simp_all add: supp_id)
        apply (subst trans[OF comp_apply[symmetric] trm.Sb_comp(1)[THEN fun_cong]])
             apply (auto simp: fun_upd_comp IImsupp_Inj_comp_bound)
        apply (rule trm.Sb_cong)
               apply (auto simp: fun_upd_comp trm.SSupp_Sb_bound trm.IImsupp_Sb_bound)
          apply (simp add: IImsupp_Inj_comp_bound2 trm.IImsupp_Sb_bound(1))
         apply (metis swap_simps(3))
        by (metis swap_def)
      done
    subgoal for X T t T2
      apply (rule disjI2, rule disjI1)
      apply (rule exE[OF MRBNF_FP.exists_fresh[where A="{X} \<union> FTVars t \<union> FVars_typ T \<union> FVars_typ T2"]])
      apply (simp add: infinite_UNIV)
      subgoal for Y
        apply (rule exI[of _ "{Y}"])
        apply (rule conjI)
         apply (auto simp: trm.Vrs_Sb) []
        apply (rule exI[of _ "{}"])
        apply (rule conjI)
         apply auto
        apply (subst trm.vvsubst_permute[symmetric])
        apply auto[4]
        apply (subst trm.map_is_Sb)
            apply (simp_all add: supp_id)
        apply (subst tvsubst_comp)
           apply (auto simp: fun_upd_comp)
        apply (rule trm.Sb_cong)
               apply (auto simp: fun_upd_comp trm.SSupp_Sb_bound trm.IImsupp_Sb_bound)
        apply (metis swap_def)+
        done
      done
    subgoal for v \<sigma> p u
      apply (rule disjI2, rule disjI2, rule disjI1)
      apply (rule mp[OF _ extend_fresh[where B="PVars p" and A="FVars v \<union> FVars u"]])
      apply (rule impI)
         apply (erule exE conjE)+
      subgoal for \<rho>
        apply (rule exI[of _ "{}"]; simp)
        apply (rule exI[of _ "\<rho> ` PVars p"]; simp)
        apply (rule conjI)
        apply (subst trm.Vrs_Sb)
            apply (auto simp: FVars_restrict infinite_UNIV intro!: finite_ordLess_infinite2 dest: match_FVars) [4]
        apply (auto simp: IImsupp_def SSupp_def restrict_def)[1]
        apply (rule exI[of _ v])
        apply (rule exI[of _ "\<sigma> o \<rho>"])
        apply (rule exI[of _ "vvsubst_pat id \<rho> p"])
        apply (rule conjI)
        apply (simp add: pat.set_map)
        apply (rule exI[of _ "permute_trm id \<rho> u"])
        apply (intro conjI)
           apply (rule Let_inject[THEN iffD2]; simp)
           apply (rule exI[of _ \<rho>])
           apply (auto simp add: id_on_def pat.set_map match_permute)
         apply (subst permute_trm_eq_tvsubst')
            apply (auto)
        apply (subst tvsubst_comp)
          apply (auto simp: supp_def[symmetric] intro!: var_class.UN_bound)
        apply (auto simp: ordLeq_ordLess_trans[OF card_of_image] pat.set_bd_UNIV)
        apply (rule trm.Sb_cong)
             apply (auto  simp: infinite_UNIV SSupp_trm_restrict restrict_def intro!: trm.SSupp_Sb_bound trm.IImsupp_Sb_bound)
        apply (subst trm.subst)
           apply (auto simp: infinite_UNIV SSupp_trm_restrict restrict_def)
        apply (subst trm.subst)
          apply (auto simp: infinite_UNIV SSupp_trm_restrict restrict_def)
        done
        apply (auto simp: infinite_UNIV intro!: trm.Un_bound trm.set_bd_UNIV)
      done
    subgoal for VV l v
      by auto
    subgoal for t t' u
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal for t t' p u
      apply (rule disjI2)+
      apply (rule mp[OF _ extend_fresh[where B="PVars p" and A="FVars t \<union> FVars t' \<union> FVars u"]])
      apply (rule impI)
         apply (erule exE conjE)+
      subgoal for \<rho>
      apply (rule exI[of _ "{}"]; simp)
      apply (rule exI[of _ "\<rho> ` PVars p"]; simp)
        apply (rule conjI)
        apply auto []
        apply (rule exI[of _ t])
        apply (rule exI[of _ t'])
        apply (rule exI[of _ "vvsubst_pat id \<rho> p"])
        apply (rule conjI)
        apply (simp add: pat.set_map)
        apply (rule exI[of _ "permute_trm id \<rho> u"])
        apply (intro conjI)
           apply (rule Let_inject[THEN iffD2]; simp)
           apply (rule exI[of _ \<rho>])
           apply (auto simp add: id_on_def pat.set_map match_permute)
           apply (rule Let_inject[THEN iffD2]; simp)
           apply (rule exI[of _ \<rho>])
           apply (auto simp add: id_on_def pat.set_map match_permute)
        done
        apply (auto simp: infinite_UNIV intro!: trm.Un_bound trm.set_bd_UNIV)
      done
    done
  done

lemma wf_ty_extend_tvsubst_typ:
  "\<turnstile> \<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta> ok \<Longrightarrow> P closed_in \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta> ok"
  apply (induct \<Delta>)
   apply auto []
  apply (auto simp: image_iff FVars_tvsubst_typ image_Un split: if_splits)
      apply (metis fst_conv)
     apply (metis fst_conv)
    apply auto[1]
   apply (smt (verit, ccfv_threshold) Un_iff fst_map_prod id_apply image_iff insert_iff
      subset_iff)
  apply auto[1]
  done

lemma wf_ty_closed_in: "\<turnstile> \<Gamma> ok \<Longrightarrow> X <: T \<in> \<Gamma> \<Longrightarrow> T closed_in \<Gamma>"
  by (induct \<Gamma>) auto

lemma ty_tvsubst_typ: "\<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
  \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X:=P)))) \<Delta> \<turnstile> tvsubst_typ (TyVar(X:=P)) S <: tvsubst_typ (TyVar(X:=P)) T"
proof (binder_induction "\<Gamma> \<^bold>, X <: Q \<^bold>, \<Delta>" S T arbitrary: \<Delta> avoiding: \<Gamma> X Q \<Delta> S T P rule: ty.strong_induct)
  case (SA_Top S \<Delta>)
  then show ?case
    apply simp
    apply (intro ty.SA_Top)
     apply (auto simp: FVars_tvsubst_typ subset_eq image_Un wf_ty_extend_tvsubst_typ image_image dest: well_scoped(1) split: if_splits)
    done
next
  case (SA_Refl_TVar Y \<Delta>)
  moreover have "P closed_in \<Gamma>"
    by (meson SA_Refl_TVar.hyps(3) well_scoped(1))
  ultimately show ?case
    by (auto simp: image_Un wf_ty_extend_tvsubst_typ image_image Domain.DomainI fst_eq_Domain
      intro!: ty_refl[of _ P] ty.SA_Refl_TVar[of _ Y])
next
  case (SA_Trans_TVar Y U T \<Delta>)
  have ok: "\<turnstile> \<Gamma> \<^bold>, X <: Q ok"
    using SA_Trans_TVar.hyps(2) wf_concatD wf_context by blast
  show ?case
  proof (cases "X = Y")
    case True
    with SA_Trans_TVar(1) have [simp]: "U = Q"
      using SA_Trans_TVar(2) context_determ wf_context by blast
    note IH = SA_Trans_TVar(3)[OF SA_Trans_TVar(4), simplified]
    from ok have "tvsubst_typ (TyVar(X := P)) Q = Q"
      by (intro trans[OF typ.Sb_cong tvsubst_typ_TyVar]) auto
    then have "\<Gamma> \<turnstile> P <: tvsubst_typ (TyVar(X := P)) Q" using SA_Trans_TVar(4) by simp
    with IH have "\<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta> \<turnstile> P <: tvsubst_typ (TyVar(X := P)) T"
      by (meson ty_transitivity2 ty_weakening wf_context)
    then show ?thesis
      by (simp add: True)
  next
    case False
    from ok have "Y <: U \<in> \<Gamma> \<Longrightarrow> tvsubst_typ (TyVar(X := P)) U = U"
      by (intro trans[OF typ.Sb_cong tvsubst_typ_TyVar])
        (auto simp: subset_iff dest: wf_ty_closed_in)
    with SA_Trans_TVar False show ?thesis
      apply auto
      apply (metis (no_types, opaque_lifting) Un_upper1 id_apply list.set_map map_prod_imageI set_append
          subset_eq ty.SA_Trans_TVar)
      done
  qed
next
  case (SA_All T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 \<Delta>)
  then show ?case
    by (subst (1 2) typ.subst) (auto dest!: SSupp_fun_upd_subset[THEN set_mp] IImsupp_fun_upd_subset[THEN set_mp])
next
  case (SA_TRec YY XX \<Delta>)
  then show ?case
    apply simp
    apply (intro ty.SA_TRec)
       apply (auto simp: wf_ty_extend_tvsubst_typ lfset.set_map image_Un image_image lfin_map_lfset
        FVars_tvsubst_typ split: if_splits dest: well_scoped(1))
       apply (meson subset_iff well_scoped(1))
      apply blast
     apply (meson subset_iff well_scoped(1))
    apply fast
    done
qed auto

lemma proj_ctxt_map[simp]: "proj_ctxt (map (map_prod id f) \<Delta>) = map (map_prod id f) (proj_ctxt \<Delta>)"
  by (auto simp: proj_ctxt_def map_filter_def filter_map o_def split_beta
    intro!: list.map_cong filter_cong split: sum.splits)

lemma wf_ctxt_extend_tvsubst_typ_aux:
  "\<turnstile> \<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> OK \<Longrightarrow> FVars_typ P \<subseteq> Inl -` dom \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta> OK"
  by (induct \<Delta>)
    (auto 0 4 simp: image_iff FVars_tvsubst_typ image_Un split: if_splits)

lemma wf_ctxt_extend_tvsubst_typ:
  "\<turnstile> \<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> OK \<Longrightarrow> P closed_in proj_ctxt \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta> OK"
  by (erule wf_ctxt_extend_tvsubst_typ_aux) (force simp: subset_eq image_iff dom_proj_ctxt)

lemma wf_ctxt_weaken_ext: "\<turnstile> \<Gamma> \<^bold>, \<Delta> OK \<Longrightarrow> \<turnstile> \<Gamma> OK"
  by (induct \<Delta>) auto

lemma wf_ctxt_closed: "\<turnstile> \<Gamma> OK \<Longrightarrow> (Inr x, T) \<in> set \<Gamma> \<Longrightarrow> FVars_typ T \<subseteq> Inl -` dom \<Gamma>"
  by (induct \<Gamma>) auto

lemmas tvsubst_typ_comp = trans[OF comp_apply[symmetric] typ.Sb_comp[THEN fun_cong]]

lemma tvsubst_typ_tvsubst_typ:
  "X \<noteq> Y \<Longrightarrow> Y \<notin> FVars_typ T \<Longrightarrow>
   tvsubst_typ (TyVar(X := T)) (tvsubst_typ (TyVar(Y := U)) Q) =
   tvsubst_typ (TyVar(Y := tvsubst_typ (TyVar(X := T)) U)) (tvsubst_typ (TyVar(X := T)) Q)"
  by (subst (1 2) tvsubst_typ_comp)
    (auto simp: typ.SSupp_Sb_bound intro!: typ.Sb_cong
       sym[OF trans[OF typ.Sb_cong tvsubst_typ_TyVar]])

lemma pat_typing_tvsubst_typ: "\<turnstile> p : T \<rightarrow> \<Delta> \<Longrightarrow>
  \<turnstile> tvsubst_pat (TyVar(X := P)) id p : tvsubst_typ (TyVar(X := P)) T \<rightarrow>
    map (map_prod id (tvsubst_typ (TyVar(X := P)))) \<Delta>"
  apply (induct p T \<Delta> rule: pat_typing.induct)
   apply (fastforce simp flip: id_def simp del: fun_upd_apply simp add: map_concat lfset.set_map lfin_map_lfset
     nonrep_PRec_def PVars_tvsubst_pat
     intro!: pat_typing.intros)+
  done

lemma typing_tvsubst_typ: "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> proj_ctxt \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
  \<Gamma> \<^bold>, map (map_prod id (tvsubst_typ (TyVar(X:=P)))) \<Delta> \<^bold>\<turnstile> tvsubst Var (TyVar(X := P)) t \<^bold>: tvsubst_typ (TyVar(X:=P)) T"
proof (binder_induction "\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>" t T arbitrary: \<Delta> avoiding: \<Gamma> X Q \<Delta> t T P rule: typing.strong_induct)
  case (TVar x T \<Delta>)
  then have "(Inr x, T) \<in> set \<Gamma> \<Longrightarrow> tvsubst_typ (TyVar(X := P)) T = T"
    by (intro trans[OF typ.Sb_cong tvsubst_typ_TyVar])
      (auto dest!: wf_ctxt_closed[rotated] dest: wf_ctxt_notin wf_ctxt_weaken_ext)
  with TVar show ?case by (force dest: well_scoped(1) simp: wf_ctxt_extend_tvsubst_typ image_iff intro!: typing.TVar)
next
  case (TTAbs Y T1 t T2 \<Delta>)
  with IImsupp_fun_upd_subset[of TyVar FVars_typ TyVar X P] show ?case apply (auto 0 3 simp: subset_eq intro!: typing.TTAbs)
    apply (subst trm.subst)
           apply (auto dest!: SSupp_fun_upd_subset[THEN set_mp])
    apply (subst typ.subst)
        apply (auto dest!: SSupp_fun_upd_subset[THEN set_mp])
    apply (auto 0 3 simp: subset_eq intro!: typing.TTAbs)
    done
next
  case (TTApp t1 Z T11 T12 T2 \<Delta>)
  have "T11 closed_in proj_ctxt (\<Gamma> \<^bold>, Inl X <: Q \<^bold>, \<Delta>)"
    using TTApp.hyps(12) well_scoped(2) by blast
  moreover
  let ?XP = "(TyVar(X := P))"
  note TTApp(11)[OF TTApp(13)]
  moreover note TTApp(12)[simplified, THEN ty_tvsubst_typ[OF _ TTApp(13)]]
  ultimately have "\<Gamma> \<^bold>, map (map_prod id (tvsubst_typ ?XP)) \<Delta> \<^bold>\<turnstile>
    TApp (tvsubst Var ?XP t1) (tvsubst_typ ?XP T2) \<^bold>:
    tvsubst_typ (TyVar(Z := tvsubst_typ ?XP T2)) (tvsubst_typ ?XP T12)"
    using IImsupp_fun_upd_subset[of TyVar FVars_typ TyVar X P] TTApp(1-9)
    apply (intro typing.TTApp)
     apply (auto simp: FVars_tvsubst_typ)
    apply (subst (asm) typ.subst)
       apply (auto simp: FVars_tvsubst_typ dest!: SSupp_fun_upd_subset[THEN set_mp])
    apply (drule set_mp, assumption)
    apply (auto simp: set_proj_ctxt)
    done
  with TTApp(1-9) show ?case
    by (subst tvsubst_typ_tvsubst_typ) auto
next
  case (TSub t S T \<Delta>)
  then show ?case
    by (force intro: typing.TSub ty_tvsubst_typ)
next
  case (TRec XX TT \<Delta>)
  then show ?case
    by (auto simp: well_scoped(1) wf_ctxt_extend_tvsubst_typ lfset.rel_map elim: lfset.rel_mono_strong intro!: typing.TRec)
next
  case (TProj ta TT l Ta \<Delta>)
  then show ?case
    by (auto intro!: typing.TProj simp: lfin_map_lfset)
next
  case (TLet ta Ta p \<Delta>' u U \<Delta>)
  then show ?case
    by (subst trm.subst)
      (auto intro!: typing.TLet pat_typing_tvsubst_typ)
qed (auto intro: typing.intros)

lemma pat_distinct[simp]:
  "nonrep_PRec PP \<Longrightarrow> PVar x T \<noteq> PRec PP"
  "nonrep_PRec PP \<Longrightarrow> PRec PP \<noteq> PVar x T"
  unfolding PVar_def PRec_def
   apply (auto simp: nonrep_PRec_alt dest!: Abs_pat_inject[THEN iffD1, rotated 2])
  apply (metis Rep_pat lfin_map_lfset mem_Collect_eq)+
  done

lemma restrict_empty[simp]: "restrict \<sigma> {} v = v"
  unfolding restrict_def by auto

lemma tvsubst_id[simp]: "tvsubst Var TyVar t = t"
  apply (binder_induction t avoiding: t rule: trm.strong_induct)
         apply (auto intro!: trans[OF lfset.map_cong_id lfset.map_id])
  apply (subst trm.subst)
      apply auto
  done

lemma labels_lfdelete[simp]: "labels (lfdelete l S) = labels S - {l}"
  including lfset.lifting
  by transfer auto

lemma distinct_labelist[simp]: "distinct (labelist S)"
  by (simp add: labelist_def)

lemma labelist_lfdelete[simp]: "labelist (lfdelete l S) = filter ((\<noteq>) l) (labelist S)"
  by (simp add: distinct_remove1_removeAll labelist_def removeAll_filter_not_eq
      sorted_list_of_set.sorted_key_list_of_set_remove)

lemma lfin_lfdelete: "(l, x) \<in>\<in> lfdelete l' S \<Longrightarrow> (l, x) \<in>\<in> S"
  including lfset.lifting
  by transfer auto

lemma lfin_lfdeleteI: "(l', x) \<in>\<in> S \<Longrightarrow> l \<noteq> l' \<Longrightarrow> (l', x) \<in>\<in> lfdelete l S"
  including lfset.lifting
  by transfer auto

lemma nonrep_PRec_lfdelete[simp]: "nonrep_PRec PP \<Longrightarrow> nonrep_PRec (lfdelete l PP)"
  unfolding nonrep_PRec_def PVars_def
  by (auto simp: lfin_lfdelete)

lemma pat_typing_tvsubst:
  assumes "\<turnstile> p : T \<rightarrow> \<Delta>" "\<Gamma> \<^bold>\<turnstile> v \<^bold>: T" "\<Gamma> \<^bold>, \<Delta> \<^bold>\<turnstile> u \<^bold>: U" "match \<sigma> p v" "PVars p \<inter> FVars v = {}"
  shows "\<Gamma> \<^bold>\<turnstile> tvsubst (restrict \<sigma> (PVars p) Var) TyVar u \<^bold>: U"
  using assms
proof (induct p T \<Delta> arbitrary: \<Gamma> v u U rule: pat_typing.induct)
  case (PVar x T)
  then show ?case
    apply (auto elim!: match.cases)
    apply (drule typing_tvsubst[where \<Delta>=\<emptyset>, simplified])
     apply assumption
    apply (erule arg_cong[where f="\<lambda>\<sigma>. _ \<^bold>\<turnstile> tvsubst \<sigma> _ _ \<^bold>: _", THEN iffD1, rotated])
    apply (auto simp: restrict_def)
    done
next
  case (PRec PP TT \<Delta> xs)
  then show ?case
    apply (auto elim!: match.cases)
    apply (frule typing_RecD[OF _ ty_refl])
      apply (simp add: typing_wf_ty)
     apply (meson typing_well_scoped)
    apply hypsubst_thin
    subgoal premises prems for VV
      using prems(1,3,5-)
      apply (induct "labelist TT" arbitrary: TT PP VV u)
      apply (frule arg_cong[where f=set], unfold set_labelist)
        apply auto []
      apply (frule arg_cong[where f=set], unfold set_labelist)
      apply (drule sym)
      apply auto
      subgoal premises prems for l ls TT PP VV u
        apply (subgoal_tac "l \<in> labels TT \<and> l \<in> labels PP \<and> l \<in> labels VV")
         defer
        using prems(2,4-) apply auto []
        apply (auto simp: labels_lfin_iff)
        subgoal for T P v
          apply (subgoal_tac "PVars P \<inter> FVars v = {}")
           defer
          subgoal
            using prems(5)
            by (force dest: Int_emptyD simp: Ball_def values_lfin_iff)
          apply (subgoal_tac " \<Gamma> \<^bold>, List.concat (map \<Delta> ls) \<^bold>\<turnstile> tvsubst (restrict \<sigma> (PVars P) Var) TyVar u \<^bold>: U")
          defer
          using prems(3)[of l P T "\<Gamma> \<^bold>, List.concat (map \<Delta> ls)" v u U] prems(4-)
           apply (auto elim!: meta_mp intro!: typing_weaken dest: typing_wf_ctxt wf_ctxt_weaken_ext)
        using prems(1)[of "lfdelete l TT" "lfdelete l PP" "tvsubst (restrict \<sigma> (PVars P) Var) TyVar u" "lfdelete l VV"] prems(2,4-)
        apply auto
        apply (drule meta_mp)
        apply (rule sym)
        using distinct_labelist[of TT]
         apply (auto simp add: filter_id_conv) []
        apply (drule meta_mp)
         apply (rule prems(3))
             apply (erule lfin_lfdelete)
            apply (erule lfin_lfdelete)
           apply assumption
          apply assumption
         apply assumption
        apply assumption
        apply (drule meta_mp)
        subgoal premises prems
          using prems(8)
          by (force dest: Int_emptyD simp: values_lfin_iff intro!: lfin_values dest!: lfin_lfdelete)
        apply (drule meta_mp)
        apply (meson lfin_lfdelete)
        apply (drule meta_mp)
         apply (meson lfin_lfdelete)
        apply fast
        apply (subst (asm) tvsubst_comp)
           apply (auto 0 0 intro!: cmin_greater) [3]
          apply (metis Int_bound2 PVars_PRec SSupp_trm_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2))
          apply (metis Int_bound2 PVars_PRec SSupp_trm_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2))
         apply auto
        apply (metis PVars_PRec nonrep_PRec_lfdelete pat.set_bd_UNIV(2))
        apply (erule arg_cong[where f="\<lambda>t. typing _ t _", THEN iffD1, rotated])
        apply (rule trm.Sb_cong)
               apply (auto 0 0 intro!: trm.SSupp_Sb_bound trm.IImsupp_Sb_bound pat.set_bd_UNIV) [5]
               apply (metis PVars_PRec nonrep_PRec_lfdelete pat.set_bd_UNIV(2))+
          apply (metis IImsupp_restrict_bound PVars_PRec pat.set_bd_UNIV(2) trm.set_bd_UNIV(1))
         apply (rule refl)
        apply (auto simp: restrict_def nonrep_PRec_def values_lfin_iff)
        subgoal for x P' l'
          apply (rule trans[OF trm.Sb_cong(1) tvsubst_id])
               apply (auto 0 0 simp: restrict_def intro!: cmin_greater)
          apply (metis Int_bound2 PVars_PRec SSupp_trm_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (metis Int_bound2 PVars_PRec SSupp_trm_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (cases "l = l'")
           apply simp
          using match_FVars[of \<sigma> P v x]
          apply (smt (verit) Int_emptyD Union_iff image_iff lfin_lfdelete subset_iff values_lfin_iff)
          apply fast
          done
        subgoal for x P' l'
          apply (subst trm.subst)
            apply (auto 0 0) [2]
            apply (metis Int_bound2 PVars_PRec SSupp_trm_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (metis IImsupp_restrict_bound PVars_PRec nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6)
              trm.set_bd_UNIV(1))
          apply (auto simp: restrict_def)
          apply (cases "l = l'")
          apply (metis lfin_label_inject)
          apply (meson lfin_lfdeleteI values_lfin_iff)
          done
        subgoal for x
          apply (subst trm.subst)
            apply (auto 0 0) [2]
            apply (metis Int_bound2 PVars_PRec SSupp_trm_restrict nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6))
          apply (metis IImsupp_restrict_bound PVars_PRec nonrep_PRec_lfdelete pat.set_bd_UNIV(2) prems(6)
              trm.set_bd_UNIV(1))
          apply (auto simp: restrict_def)
          apply (metis lfin_lfdelete values_lfin_iff)
          done
        done
      done
    done
  done
qed

lemma preservation: "\<Gamma> \<^bold>\<turnstile> t \<^bold>: T \<Longrightarrow> step t t' \<Longrightarrow> \<Gamma> \<^bold>\<turnstile> t' \<^bold>: T"
proof (binder_induction \<Gamma> t T arbitrary: t' avoiding: \<Gamma> T t t' rule: typing.strong_induct)
  case (TApp \<Gamma> t1 T11 T12 t2 t')
  from TApp(3,1,2,4-) show ?case
    apply (binder_induction "App t1 t2" t' avoiding: \<Gamma> rule: step.strong_induct)
    subgoal for v x T t
      apply clarsimp
      apply (frule typing_AbsD)
        apply fastforce
       apply (rule ty_refl)
      using typing_wf_ty apply blast
      using typing_well_scoped apply blast
      apply safe
      apply (drule typing_tvsubst[where \<Delta>=\<emptyset>, simplified])
       apply (erule (1) TSub[rotated])
      apply (erule (1) TSub)
      done
       apply (auto intro: typing.intros)
    done
next
  case (TTApp \<Gamma> t1 X T11 T12 T2 t')
  from TTApp(8,1-7,9) show ?case
    apply (binder_induction "TApp t1 T2" t' avoiding: \<Gamma> X T11 T12 rule: step.strong_induct)
        prefer 2
    subgoal for Y T t U
      apply clarsimp
      apply (frule typing_TAbsD[where ?U1.0 = T11 and ?U2.0 = "permute_typ (X \<leftrightarrow> Y) T12"])
          apply (fastforce+) [3]
      apply (metis ty_refl typ.inject(3) typing_well_scoped typing_wf_ctxt wf_ty_proj_ctxt)
      apply (subst Forall_eq_tvsubst_typ[of _ _ _ Y "permute_typ (X \<leftrightarrow> Y) T12"])
      using typ.inject(3) apply blast
      apply (erule exE conjE)+
      apply (rule typing_tvsubst_typ[where \<Delta>=\<emptyset>, simplified])
       apply (erule TSub)
       apply (simp add: fun_upd_twist)
      apply assumption
      done
    apply (force intro: typing.intros)+
    done
next
  case (TRec \<Gamma> XX TT t')
  then show ?case
    apply -
    apply (erule step.cases)
             apply (auto intro!:typing.TRec  simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id]
      lfin_map_lfset values_lfin_iff subset_eq Ball_def)
    by (smt (z3) fst_conv lfin_lfupdate lfupdate_idle map_lfset_lfupdate snd_conv)
next
  case (TProj \<Gamma> ta TT l Ta t')
  then have "\<turnstile> proj_ctxt \<Gamma> ok" "TRec TT closed_in proj_ctxt \<Gamma>"
    by (force dest: typing_wf_ty typing_well_scoped)+
  with TProj show ?case
    apply -
    apply (erule step.cases)
    apply (auto intro: typing.TProj dest!: typing_RecD[OF _ ty_refl])
    done
next
  case (TLet \<Gamma> t T p \<Delta> u U t')
  from TLet(7,1-6,8-) show ?case
    apply (binder_induction "Let p t u" t' avoiding: \<Gamma> p t u t' rule: step.strong_induct)
             apply (auto simp: Let_inject)
    subgoal for \<sigma> p' u' \<rho>
      apply (rule rev_mp[OF ex_avoiding_bij[of \<rho> "FVars u' - PVars p'" "PVars p \<union> PVars p'" "Inr -` dom \<Gamma>"]]; (simp add: infinite_UNIV)?)
      subgoal by (fastforce simp: pat.set_map)
      subgoal
        by (metis List.finite_set finite_imageI finite_ordLess_infinite2 finite_vimageI
            infinite_UNIV inj_Inr)
      apply (rule impI)
      apply (erule exE conjE)+
      subgoal for \<rho>'
        apply clarsimp
        apply (subgoal_tac "vvsubst_pat id \<rho> p' = vvsubst_pat id \<rho>' p'")
        apply (subgoal_tac "permute_trm id \<rho> u' = permute_trm id \<rho>' u'")
        subgoal
        apply simp
      apply (rule pat_typing_tvsubst)
      apply (drule pat_typing_equiv[of id "inv \<rho>'", rotated 4]; (simp add: supp_inv_bound pat.map_comp)?)
       apply assumption
      apply (frule typing.equiv[of id "inv \<rho>'" "\<Gamma> \<^bold>, \<Delta>", rotated 4])
          apply (auto simp: supp_inv_bound)
          apply (subgoal_tac "map (map_prod (map_sum id (inv \<rho>')) id) \<Gamma> = \<Gamma>")
          apply (auto simp: supp_inv_bound trm.permute_comp trm.permute_id) []
          apply (intro list.map_ident_strong sum.map_ident_strong prod.map_ident_strong; simp?)
          using imsupp_id_on[of "inv \<rho>'" "Inr -` SystemFSub.dom \<Gamma>"]
          apply (force simp: imsupp_inv id_on_def image_iff elim!: setr.cases)
          done
        subgoal
          apply (auto 0 0 simp: id_on_def intro!: trm.permute_cong) []
          apply (metis (no_types, lifting) PVars_vvsubst_pat TLet.fresh(1) UN_I
              disjoint_iff_not_equal image_eqI setr.intros)
          done
        subgoal
          apply (auto 0 0 simp: id_on_def intro!: pat.map_cong) []
          apply (metis (no_types, lifting) PVars_vvsubst_pat TLet.fresh(1) UN_I
              disjoint_iff_not_equal image_eqI setr.intros)
          done
        done
      done
    apply (metis Let_inject typing.TLet)
    done
qed (auto elim: step.cases intro: typing.TSub)

end
