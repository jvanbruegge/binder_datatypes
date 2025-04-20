theory Pi_Transition_Common
  imports Commitment
begin

hide_const inverse_class.inverse_divide trans
no_notation inverse.inverse_divide (infixl "'/" 70)

abbreviation Tsupp :: "trm \<Rightarrow> cmt \<Rightarrow> var set" where
"Tsupp e1 e2 \<equiv> FFVars e1 \<union> FVars_commit e2"

(* Supply of fresh variables: *)
lemma finite_Tsupp: "finite (Tsupp e1 e2)"
  by (metis commit.set(4) finite_FVars_commit finite_Un)

lemma finite_vars: "finite (vars act)"
  by (cases act) auto

lemma exists_fresh':
"\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set as. z \<notin> vars t) \<and> (z \<notin> Tsupp x1 x2)"
proof-
  have 0: "|set xs \<union> Tsupp x1 x2 \<union> \<Union> (vars ` (set as))| <o |UNIV::var set|"
  unfolding ls_UNIV_iff_finite
  using finite_Tsupp finite_vars by blast
  then obtain x where "x \<notin> set xs \<union> Tsupp x1 x2 \<union> \<Union> (vars ` (set as))"
    using MRBNF_FP.exists_fresh by blast
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

lemma R_forw_subst: "R x y \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> R (f x) (g y)) \<Longrightarrow> z = g y \<Longrightarrow> R (f x) z"
  by blast

lemma FVars_commit_Cmt: "FVars_commit (Cmt act P) = fvars act \<union> (FFVars P - bvars act)"
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

lemma fra_empty[simp]: "fra \<alpha> \<longleftrightarrow> bns \<alpha> = {}"
  by (cases \<alpha>) auto

lemma exists_fresh:
  "\<exists> z. z \<notin> set xs \<and> (z \<notin> Tsupp x1 x2)"
proof-
  have 0: "|set xs \<union> Tsupp x1 x2| <o |UNIV::var set|"
    unfolding ls_UNIV_iff_finite
    using finite_Tsupp by blast
  then obtain x where "x \<notin> set xs \<union> Tsupp x1 x2"
    using MRBNF_FP.exists_fresh by blast
  thus ?thesis by auto
qed

lemma ns_alt: "ns \<alpha> = bns \<alpha> \<union> fns \<alpha>"
  by (cases \<alpha>) auto

lemma vars_alt: "vars \<alpha> = bns \<alpha> \<union> fns \<alpha>"
  by (cases \<alpha>) auto

fun rrename_bound_action where
  "rrename_bound_action f (finp x y) = finp x y"
| "rrename_bound_action f (fout x y) = fout x y"
| "rrename_bound_action f (bout x y) = bout x (f y)"
| "rrename_bound_action f (binp x y) = binp x (f y)"
| "rrename_bound_action f tau = tau"

lemma bvars_rrename_bound_action[simp]: "bvars (rrename_bound_action f \<alpha>) = f ` bvars \<alpha>"
  by (cases \<alpha>) auto

lemma Cmt_rrename_bound_action: "bij (f :: var \<Rightarrow> var) \<Longrightarrow> |supp f| <o |UNIV :: var set| \<Longrightarrow> id_on (FFVars P - bvars \<alpha>) f \<Longrightarrow>
  Cmt \<alpha> P = Cmt (rrename_bound_action f \<alpha>) (rrename f P)"
  apply (cases \<alpha>)
  by (auto simp: Bout_inject Binp_inject swap_apply_fresh_bij2 id_on_def bij_implies_inject intro!: exI[of _ f] term.permute_cong_id[symmetric] term.permute_cong)+
  

lemma Cmt_rrename_bound_action_Par: "bij (f :: var \<Rightarrow> var) \<Longrightarrow> |supp f| <o |UNIV :: var set| \<Longrightarrow> id_on (FFVars P \<union> FFVars Q - bvars \<alpha>) f \<Longrightarrow>
  Cmt \<alpha> (P \<parallel> Q) = Cmt (rrename_bound_action f \<alpha>) (rrename f P \<parallel> rrename f Q)"
  by (subst Cmt_rrename_bound_action[of f]) auto

end