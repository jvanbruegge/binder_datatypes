theory Pi_Transition_Common
  imports Commitment
begin

hide_const inverse_class.inverse_divide trans
no_notation inverse.inverse_divide (infixl "'/" 70)

abbreviation Tsupp :: "trm \<Rightarrow> cmt \<Rightarrow> var set" where 
"Tsupp e1 e2 \<equiv> FFVars e1 \<union> FFVars_commit e2"

(* Supply of fresh variables: *)
lemma finite_Tsupp: "finite (Tsupp e1 e2)"
  by (metis FFVars_commit_simps(5) finite_FFVars_commit finite_Un)

lemma finite_vars: "finite (vars act)"
  by (cases act) auto

lemma exists_fresh':
"\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set as. z \<notin> vars t) \<and> (z \<notin> Tsupp x1 x2)"
proof-
  have 0: "|set xs \<union> Tsupp x1 x2 \<union> \<Union> (vars ` (set as))| <o |UNIV::var set|" 
  unfolding ls_UNIV_iff_finite
  using finite_Tsupp finite_vars by blast
  then obtain x where "x \<notin> set xs \<union> Tsupp x1 x2 \<union> \<Union> (vars ` (set as))"
  by (meson ex_new_if_finite finite_iff_le_card_var 
    infinite_iff_natLeq_ordLeq var_term_pre_class.large)
  thus ?thesis by auto
qed

ML \<open>fun gen_fresh ctxt xs0 acts0 ts0 = HEADGOAL (Subgoal.FOCUS_PARAMS (fn {context = ctxt, params = cps, ...} =>
  let
    val ps = map (Thm.term_of o snd) cps;
    fun mk zs T = filter (fn t => fastype_of t = T) ps |> append zs |> HOLogic.mk_list T |> Thm.cterm_of ctxt;
    val xs = mk xs0 @{typ var};
    val acts = mk acts0 @{typ "var action"};
    (*val tss = map (mk ts0) [@{typ "var term"}, @{typ "var commit"}];*)
    val thm = infer_instantiate' ctxt ([SOME xs, SOME acts] @ map (SOME o Thm.cterm_of ctxt) ts0) @{thm exists_fresh'} RS exE;
  in HEADGOAL (resolve_tac ctxt [thm]) end) ctxt)\<close>

lemma isPerm_swap: "isPerm (id(x := y, y := x))"
  by (auto simp: isPerm_def MRBNF_FP.supp_swap_bound infinite_UNIV)

lemma R_forw_subst: "R x y \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> R (f x) (g y)) \<Longrightarrow> z = g y \<Longrightarrow> R (f x) z"
  by blast

lemma FFVars_commit_Cmt: "FFVars_commit (Cmt act P) = fvars act \<union> (FFVars P - bvars act)"
  by (cases act) auto

lemma empty_bvars_vars_fvars: "bvars act = {} \<Longrightarrow> vars act = fvars act"
  by (cases act) auto

lemma bvars_swapa: "bvars act = {} \<Longrightarrow> bvars (swapa act x xx) = {}"
  by (cases act) auto

lemma fvars_swapa: "xx \<in> fvars (swapa act x xx) \<longleftrightarrow> x \<in> fvars act"
  by (cases act) auto

lemma swapa_idle: "xx \<notin> vars act \<Longrightarrow> x \<notin> vars act \<Longrightarrow> swapa act x xx = act"
  by (cases act) auto

lemmas act_var_simps = empty_bvars_vars_fvars bvars_swapa fvars_swapa swapa_idle

lemma small_bns[simp]: "small (bns \<alpha>)"
  by (cases \<alpha>) auto

lemma small_ns[simp]: "small (ns \<alpha>)"
  by (cases \<alpha>) auto

lemma exists_fresh:
  "\<exists> z. z \<notin> set xs \<and> (z \<notin> Tsupp x1 x2)"
proof-
  have 0: "|set xs \<union> Tsupp x1 x2| <o |UNIV::var set|"
    unfolding ls_UNIV_iff_finite
    using finite_Tsupp by blast
  then obtain x where "x \<notin> set xs \<union> Tsupp x1 x2"
    by (meson ex_new_if_finite finite_iff_le_card_var
        infinite_iff_natLeq_ordLeq var_term_pre_class.large)
  thus ?thesis by auto
qed

end