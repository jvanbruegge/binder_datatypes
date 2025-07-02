theory Expr
  imports "Binders.MRBNF_Recursor"
begin

declare supp_id_bound[simp]

declare [[mrbnf_internals]]

binder_datatype 'a expr =
  Var 'a
  | Lam x::'a t::"'a expr" binds x in t
  | App "'a expr" "'a expr"

lemma tvsubst_expr_unique:
  assumes 
    B: "|- B| <o |UNIV :: 'a set|" and
    \<rho>: "|SSupp_expr (\<rho> :: 'a::var \<Rightarrow> 'a expr)| <o |UNIV :: 'a set|" and
    A: "|A| <o |UNIV :: 'a set|" and
    base: "\<And>a. a \<in> B \<Longrightarrow> h (Var a) = \<rho> a" and
    step: "\<And>u. FVars_expr (expr_ctor u) \<subseteq> B \<Longrightarrow>
    set2_expr_pre u \<inter> A = {} \<Longrightarrow>
    set2_expr_pre u \<inter> IImsupp_expr \<rho> = {} \<Longrightarrow>
    noclash_expr u \<Longrightarrow>
    (\<forall>a. expr_ctor u \<noteq> Var a) \<Longrightarrow>
    h (expr_ctor u) = expr_ctor (map_expr_pre id id h h u)"
  shows "FVars_expr e \<subseteq> B \<Longrightarrow> h e = tvsubst_expr \<rho> e"
  apply (binder_induction e avoiding: A "IImsupp_expr \<rho>" e "- B" rule: expr.strong_induct)
  subgoal
    apply (rule A)
    done
  subgoal
    apply (simp add: IImsupp_expr_def)
    apply (rule Un_bound[OF infinite_UNIV])
     apply (rule \<rho>)
    apply (rule UN_bound)
     apply (rule \<rho>)
    apply (rule expr.FVars_bd_UNIVs)
    done
  subgoal
    apply (rule B)
    done
  subgoal for x
    using expr.tvsubst_VVr[OF ordLess_ordLeq_trans[OF \<rho>], of x]
    apply (subst base)
     apply simp
    apply (simp add: tvVVr_tvsubst_expr_def Var_def tv\<eta>_expr_tvsubst_expr_def)
    done
  subgoal premises prems for x t
    using prems unfolding Lam_def
    apply (subst step)
         apply (simp_all add: expr.FVars_ctor noclash_expr_def Var_def expr.TT_inject0
        set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
        Abs_expr_pre_inverse Abs_expr_pre_inject expr.FVars_permute)
    apply (subst expr.tvsubst_cctor_not_isVVr)
        apply (simp_all add: assms(1) noclash_expr_def expr.TT_inject0 tvisVVr_tvsubst_expr_def tvVVr_tvsubst_expr_def tv\<eta>_expr_tvsubst_expr_def
        set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
        Abs_expr_pre_inverse Abs_expr_pre_inject \<rho>)
    apply (rule exI[of _ id]; simp add: expr.permute_id)
    apply blast
    done
  subgoal for t u
    unfolding App_def
    apply (subst step)
         apply (simp_all add: expr.FVars_ctor noclash_expr_def Var_def expr.TT_inject0
        set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
        Abs_expr_pre_inverse Abs_expr_pre_inject)
    apply (subst expr.tvsubst_cctor_not_isVVr)
        apply (simp_all add: assms(1) noclash_expr_def expr.TT_inject0 tvisVVr_tvsubst_expr_def tvVVr_tvsubst_expr_def tv\<eta>_expr_tvsubst_expr_def
        set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
        Abs_expr_pre_inverse Abs_expr_pre_inject \<rho>)
    done
  done

end