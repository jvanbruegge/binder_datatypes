theory Commitment
imports Pi  "Prelim.Curry_LFP" "Binders.Generic_Barendregt_Enhanced_Rule_Induction"
begin

local_setup \<open>fn lthy =>
let
  val name1 = "commit_internal"
  val name2 = "commit"
  val T1 = @{typ "'var term"}
  val T2 = @{typ "'var * 'var * 'var term +'var * 'var * 'var term + 'var * 'bvar * 'brec + 'var term + 'var * 'bvar * 'brec"}
  val Xs = map dest_TFree []
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'bvar}, @{typ 'brec}, @{typ 'rec}]
  val rel = [[0]]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify1 = Binding.prefix_name (name1 ^ "_pre_")
  val qualify2 = Binding.prefix_name (name2 ^ "_pre_")

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf1, tys1), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify1 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T1
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf2, tys2), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify2 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T2
    (accum, lthy);

  val (tys, _, (mrbnfs as [mrbnf1, mrbnf2], (accum, lthy))) =
      MRBNF_Comp.normalize_mrbnfs (K I) [] (map (map dest_TFree) [snd tys1, snd tys2])
      [] [] (K (resBs @ Xs)) NONE [mrbnf1, mrbnf2] (accum, lthy);

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf1, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name1 ^ "_pre")) true (fst tys1) [] mrbnf1 lthy
  val ((mrbnf2, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name2 ^ "_pre")) true (fst tys2) [] mrbnf2 lthy

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf1, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf1 lthy
  val (bnf2, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf2 lthy

  (* Step 4: Create fixpoint of pre-MRBNF *)
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [
    ((name1, mrbnf1), 1), ((name2, mrbnf2), 1)
  ] rel lthy;
in lthy end
\<close>
print_theorems


(* Monomorphization: *)
type_synonym cmt = "var commit"
instance var :: var_commit_pre by standard
instance var :: var_commit_internal_pre by standard

definition Finp :: "var \<Rightarrow> var \<Rightarrow> trm \<Rightarrow> cmt" where
  "Finp x y t \<equiv> commit_ctor (Abs_commit_pre (Inl (x, y, t)))"
definition Fout :: "var \<Rightarrow> var \<Rightarrow> trm \<Rightarrow> cmt" where
  "Fout x y t \<equiv> commit_ctor (Abs_commit_pre (Inr (Inl (x, y, t))))"
definition Bout :: "var \<Rightarrow> var \<Rightarrow> trm \<Rightarrow> cmt" where
  "Bout x y t \<equiv> commit_ctor (Abs_commit_pre (Inr (Inr (Inl (x, y, commit_internal_ctor (Abs_commit_internal_pre t))))))"
definition Tau :: "trm \<Rightarrow> cmt" where
  "Tau t \<equiv> commit_ctor (Abs_commit_pre (Inr (Inr (Inr (Inl t)))))"
definition Binp :: "var \<Rightarrow> var \<Rightarrow> trm \<Rightarrow> cmt" where
  "Binp x y t \<equiv> commit_ctor (Abs_commit_pre (Inr (Inr (Inr (Inr (x, y, commit_internal_ctor (Abs_commit_internal_pre t)))))))"

lemmas toUnfold = set1_commit_internal_pre_def
  UN_empty UN_empty2 UN_single Un_empty_left Un_empty_right
  comp_def empty_Diff
  map_prod_simp prod_set_simps
  map_sum.simps sum_set_simps prod_set_simps
  Sup_empty cSup_singleton
  (* *)
  Abs_commit_pre_inverse[OF UNIV_I]
  set1_commit_pre_def set2_commit_pre_def set4_commit_pre_def set3_commit_pre_def
  Abs_commit_internal_pre_inverse[OF UNIV_I]
  set1_commit_internal_pre_def set2_commit_internal_pre_def
  set3_commit_internal_pre_def set4_commit_internal_pre_def

lemma FFVars_commit_simps[simp]:
  "FFVars_commit (Finp x y t) = {x, y} \<union> FFVars t"
  "FFVars_commit (Fout x y t) = {x, y} \<union> FFVars t"
  "FFVars_commit (Binp x y t) = {x} \<union> (FFVars t - {y})"
  "FFVars_commit (Bout x y t) = {x} \<union> (FFVars t - {y})"
  "FFVars_commit (Tau t) = FFVars t"
  apply (unfold Binp_def Bout_def Finp_def Fout_def Tau_def)
  apply (unfold commit_internal.FFVars_cctors(2))
  apply (unfold toUnfold)
      apply (unfold commit_internal.FFVars_cctors(1))
  apply (unfold toUnfold)
  apply auto
  done

lemmas commit_pre.map_id0[simp]
lemmas commit_pre_map_cong_id = commit_pre.map_cong[of _ _ "id::var\<Rightarrow>var" "id::var\<Rightarrow>var" _ _ _ id _ id, simplified]

lemma map_commit_pre_Inl_aux: "bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow>
 map_commit_pre (id::var\<Rightarrow>var) (f::var\<Rightarrow>var) (rrename_commit_internal f) id (Abs_commit_pre (Inl (x, y, P))) =
 Abs_commit_pre (Inl (x, y, P))"
apply(rule commit_pre_map_cong_id) unfolding toUnfold by auto

lemma map_commit_pre_Inr_Inl_aux: "bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow>
 map_commit_pre (id::var\<Rightarrow>var) (f::var\<Rightarrow>var) (rrename_commit_internal f) id (Abs_commit_pre (Inr (Inl (x, y, P)))) =
 Abs_commit_pre (Inr (Inl (x, y, P)))"
apply(rule commit_pre_map_cong_id) unfolding toUnfold by auto

lemma map_commit_pre_Inr_Inr_Inl_aux: "bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow>
 map_commit_pre id f (rrename_commit_internal f) id
          (Abs_commit_pre (Inr (Inr (Inl (x::var, y::var, commit_internal_ctor (Abs_commit_internal_pre P)))))) =
 Abs_commit_pre (Inr (Inr (Inl (x, f y, commit_internal_ctor (Abs_commit_internal_pre (rrename f P))))))"
unfolding map_commit_pre_def toUnfold apply auto
unfolding commit_internal.rrename_cctors(1)
unfolding map_commit_internal_pre_def by (simp add: toUnfold(27))

lemma map_commit_pre_Inr_Inr_Inr_Inl_aux: "bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow>
 map_commit_pre (id::var\<Rightarrow>var) (f::var\<Rightarrow>var) (rrename_commit_internal f) id (Abs_commit_pre (Inr (Inr (Inr (Inl P))))) =
 Abs_commit_pre (Inr (Inr (Inr (Inl P))))"
apply(rule commit_pre_map_cong_id) unfolding toUnfold by auto

lemma map_commit_pre_Inr_Inr_Inr_Inr_aux: "bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow>
 map_commit_pre (id::var\<Rightarrow>var) (f::var\<Rightarrow>var) (rrename_commit_internal f) id (Abs_commit_pre (Inr (Inr (Inr (Inr (x::var, y::var, commit_internal_ctor (Abs_commit_internal_pre P))))))) =
 Abs_commit_pre (Inr (Inr (Inr (Inr (x, f y, commit_internal_ctor (Abs_commit_internal_pre (rrename f P)))))))"
unfolding map_commit_pre_def toUnfold apply auto
unfolding commit_internal.rrename_cctors(1)
unfolding map_commit_internal_pre_def by (simp add: toUnfold(27))

lemma Abs_commit_pre_inj[simp]: "Abs_commit_pre k = Abs_commit_pre k' \<longleftrightarrow> k = k'"
by (metis toUnfold(22))

lemma Abs_commit_internal_pre_inj[simp]: "Abs_commit_internal_pre k = Abs_commit_internal_pre k' \<longleftrightarrow> k = k'"
by (metis toUnfold(27))

lemma Finp_inj[simp]: "Finp x y P = Finp x' y' P' \<longleftrightarrow> x = x' \<and> y = y' \<and> P = P'"
unfolding Finp_def unfolding commit_internal.TT_injects0 apply simp
unfolding toUnfold apply auto
  subgoal for f apply(subst (asm) map_commit_pre_Inl_aux) by auto
  subgoal for f apply(subst (asm) map_commit_pre_Inl_aux) by auto
  subgoal for f apply(subst (asm) map_commit_pre_Inl_aux) by auto
  subgoal apply(rule exI[of _ id]) apply(subst map_commit_pre_Inl_aux) by auto .

lemma Fout_inj[simp]: "Fout x y P = Fout x' y' P' \<longleftrightarrow> x = x' \<and> y = y' \<and> P = P'"
unfolding Fout_def unfolding commit_internal.TT_injects0 apply simp
unfolding toUnfold apply auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inl_aux) by auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inl_aux) by auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inl_aux) by auto
  subgoal apply(rule exI[of _ id]) apply(subst map_commit_pre_Inr_Inl_aux) by auto .

lemma Bout_inj[simp]: "Bout x y P = Bout x' y' P' \<longleftrightarrow> x = x' \<and> ((y' \<notin> FFVars P \<or> y' = y) \<and> P' = swap P y y')"
unfolding Bout_def unfolding commit_internal.TT_injects0 apply simp
unfolding toUnfold apply auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inr_Inl_aux) by auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inr_Inl_aux)
  unfolding id_on_def apply auto unfolding commit_internal.FFVars_cctors(1) toUnfold by auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inr_Inl_aux)
  unfolding id_on_def apply auto unfolding commit_internal.FFVars_cctors(1) toUnfold
  unfolding commit_internal.TT_injects0(1) id_on_def
  unfolding map_commit_internal_pre_def apply (auto simp: toUnfold id_on_def)
  apply(rule rrename_cong) by auto
  subgoal apply(rule exI[of _ "(id(y:=y',y':=y))"])
  apply(subst map_commit_pre_Inr_Inr_Inl_aux) apply auto
  unfolding commit_internal.FFVars_cctors(1) by (auto simp: toUnfold id_on_def)
  subgoal apply(rule exI[of _ "(id(y:=y',y':=y))"])
  apply(subst map_commit_pre_Inr_Inr_Inl_aux) by auto .

lemma Binp_inj[simp]: "Binp x y P = Binp x' y' P' \<longleftrightarrow> x = x' \<and> ((y' \<notin> FFVars P \<or> y' = y) \<and> P' = swap P y y')"
unfolding Binp_def unfolding commit_internal.TT_injects0 apply simp
unfolding toUnfold apply auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inr_Inr_Inr_aux) by auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inr_Inr_Inr_aux)
  unfolding id_on_def apply auto unfolding commit_internal.FFVars_cctors(1) toUnfold by auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inr_Inr_Inr_aux)
  unfolding id_on_def apply auto unfolding commit_internal.FFVars_cctors(1) toUnfold
  unfolding commit_internal.TT_injects0(1) id_on_def
  unfolding map_commit_internal_pre_def apply (auto simp: toUnfold id_on_def)
  apply(rule rrename_cong) by auto
  subgoal apply(rule exI[of _ "(id(y:=y',y':=y))"])
  apply(subst map_commit_pre_Inr_Inr_Inr_Inr_aux) apply auto
  unfolding commit_internal.FFVars_cctors(1) by (auto simp: toUnfold id_on_def)
  subgoal apply(rule exI[of _ "(id(y:=y',y':=y))"])
  apply(subst map_commit_pre_Inr_Inr_Inr_Inr_aux) by auto .

lemma Tau_inj[simp]: "Tau P = Tau P' \<longleftrightarrow> P = P'"
unfolding Tau_def unfolding commit_internal.TT_injects0 apply simp
unfolding toUnfold apply auto
  subgoal for f apply(subst (asm) map_commit_pre_Inr_Inr_Inr_Inl_aux) by auto
  subgoal apply(rule exI[of _ id]) apply(subst map_commit_pre_Inr_Inr_Inr_Inl_aux) by auto .

(* *)

lemma Finp_Fout_diff[simp]: "Finp x y P \<noteq> Fout x' y' P'"
unfolding Finp_def Fout_def
by (metis Abs_commit_pre_inj Inl_Inr_False commit_internal.TT_injects0(2) map_commit_pre_Inl_aux)

lemmas Fout_Finp_diff[simp] = Finp_Fout_diff[symmetric]

lemma Finp_Bout_diff[simp]: "Finp x y P \<noteq> Bout x' y' P'"
unfolding Finp_def Bout_def
by (metis Abs_commit_pre_inj Inl_Inr_False commit_internal.TT_injects0(2) map_commit_pre_Inl_aux)

lemmas Bout_Finp_diff[simp] = Finp_Bout_diff[symmetric]

lemma Finp_Tau_diff[simp]: "Finp x y P \<noteq> Tau P'"
unfolding Finp_def Tau_def
by (metis Abs_commit_pre_inj Inl_Inr_False commit_internal.TT_injects0(2) map_commit_pre_Inl_aux)

lemmas Tau_Finp_diff[simp] = Finp_Tau_diff[symmetric]

lemma Fout_Bout_diff[simp]: "Fout x y P \<noteq> Bout x' y' P'"
unfolding Fout_def Bout_def
by (metis Abs_commit_pre_inj Inl_Inr_False commit_internal.TT_injects0(2) map_commit_pre_Inr_Inl_aux sum.inject(2))

lemmas Bout_Fout_diff[simp] = Fout_Bout_diff[symmetric]

lemma Fout_Tau_diff[simp]: "Fout x y P \<noteq> Tau P'"
unfolding Fout_def Tau_def
by (metis Abs_commit_pre_inj Inl_Inr_False commit_internal.TT_injects0(2) map_commit_pre_Inr_Inl_aux sum.inject(2))

lemmas Tau_Fout_diff[simp] = Fout_Tau_diff[symmetric]

lemma Bout_Tau_diff[simp]: "Bout x y P \<noteq> Tau P'"
unfolding Bout_def Tau_def
by (smt (verit) Inl_Inr_False Inr_inject commit_internal.TT_injects0(2) map_commit_pre_Inr_Inr_Inl_aux toUnfold(22))

lemma Binp_Boutp_diff[simp]: "Binp x y P \<noteq> Bout x' y' P'"
  unfolding Binp_def Bout_def
  by (smt (verit) Inl_Inr_False Inr_inject commit_internal.TT_injects0(2) map_commit_pre_Inr_Inr_Inl_aux toUnfold(22))

lemma Binp_Finp_diff[simp]: "Binp x y P \<noteq> Finp x' y' P'"
  unfolding Binp_def Finp_def
  by (metis Abs_commit_pre_inj Inl_Inr_False commit_internal.TT_injects0(2) map_commit_pre_Inl_aux)

lemma Binp_Fout_diff[simp]: "Binp x y P \<noteq> Fout x' y' P'"
  unfolding Binp_def Fout_def
  by (metis Abs_commit_pre_inj Inl_Inr_False Inr_inject commit_internal.TT_injects0(2) map_commit_pre_Inr_Inl_aux)

lemma Binp_Tau_diff[simp]: "Binp x y P \<noteq> Tau P'"
  unfolding Binp_def Tau_def
  by (metis Abs_commit_pre_inj Inr_not_Inl commit_internal.TT_injects0(2) map_commit_pre_Inr_Inr_Inr_Inl_aux old.sum.inject(2))

lemmas Tau_Bout_diff[simp] = Bout_Tau_diff[symmetric]

(* Supply of fresh variables *)

lemma finite_FFVars_commit: "finite (FFVars_commit C)"
unfolding ls_UNIV_iff_finite[symmetric]
by (simp add: commit_internal.card_of_FFVars_bounds(2))

lemma exists_fresh:
"\<exists> z. z \<notin> set xs \<and> (\<forall>P \<in> set Cs. z \<notin> FFVars_commit P)"
proof-
  have 0: "|set xs \<union> \<Union> (FFVars_commit ` (set Cs))| <o |UNIV::var set|"
  unfolding ls_UNIV_iff_finite
  using finite_FFVars_commit by blast
  then obtain x where "x \<notin> set xs \<union> \<Union> (FFVars_commit ` (set Cs))"
  by (meson ex_new_if_finite finite_iff_le_card_var
    infinite_iff_natLeq_ordLeq var_term_pre_class.large)
  thus ?thesis by auto
qed

(* *)

lemma rrename_commit_Finp[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>
  rrename_commit \<sigma> (Finp a u P) = Finp (\<sigma> a) (\<sigma> u) (rrename \<sigma> P)"
unfolding Finp_def unfolding commit_internal.rrename_cctors
unfolding map_commit_pre_def unfolding toUnfold by simp

lemma rrename_commit_Fout[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>
  rrename_commit \<sigma> (Fout a u P) = Fout (\<sigma> a) (\<sigma> u) (rrename \<sigma> P)"
unfolding Fout_def unfolding commit_internal.rrename_cctors
unfolding map_commit_pre_def unfolding toUnfold by simp

lemma rrename_commit_Bout[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>
  rrename_commit \<sigma> (Bout a u P) = Bout (\<sigma> a) (\<sigma> u) (rrename \<sigma> P)"
unfolding Bout_def unfolding commit_internal.rrename_cctors
unfolding map_commit_pre_def unfolding toUnfold
unfolding commit_internal.rrename_cctors(1)
unfolding map_commit_internal_pre_def unfolding toUnfold by simp

lemma rrename_commit_Binp[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>
  rrename_commit \<sigma> (Binp a u P) = Binp (\<sigma> a) (\<sigma> u) (rrename \<sigma> P)"
unfolding Binp_def unfolding commit_internal.rrename_cctors
unfolding map_commit_pre_def unfolding toUnfold
unfolding commit_internal.rrename_cctors(1)
unfolding map_commit_internal_pre_def unfolding toUnfold by simp

lemma rrename_commit_Tau[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>
  rrename_commit \<sigma> (Tau P) = Tau (rrename \<sigma> P)"
unfolding Tau_def unfolding commit_internal.rrename_cctors
unfolding map_commit_pre_def unfolding toUnfold
unfolding commit_internal.rrename_cctors(1)
unfolding map_commit_internal_pre_def unfolding toUnfold by simp

(* Actions *)

datatype (vars:'a) action = finp 'a 'a | fout 'a 'a | is_bout: bout 'a 'a | binp 'a 'a | tau

lemmas action.set_map[simp]

type_synonym act = "var action"

fun Cmt :: "act \<Rightarrow> trm \<Rightarrow> cmt" where
 "Cmt (finp x y) P = Finp x y P"
|"Cmt (fout x y) P = Fout x y P"
|"Cmt (bout x y) P = Bout x y P"
|"Cmt (binp x y) P = Binp x y P"
|"Cmt tau P = Tau P"

fun bns :: "act \<Rightarrow> var set" where
 "bns (bout x y) = {y}"
|"bns (binp x y) = {y}"
|"bns _ = {}"

fun fns :: "act \<Rightarrow> var set" where
 "fns (bout x y) = {x}"
|"fns (binp x y) = {x}"
|"fns act = vars act"

fun fra :: "act \<Rightarrow> bool" where
  "fra (finp _ _) = True"
| "fra (fout _ _) = True"
| "fra tau = True"
| "fra _ = False"

fun ns :: "act \<Rightarrow> var set" where
  "ns (binp x y) = {x, y}"
| "ns (bout x y) = {x, y}"
| "ns (finp x y) = {x, y}"
| "ns (fout x y) = {x, y}"
| "ns tau = {}"

abbreviation "bvars \<equiv> bns"
abbreviation "fvars \<equiv> fns"

lemma bns_bound: "|bns \<alpha>| <o |UNIV::'a::var_commit_pre set|"
  by (metis Commitment.var_ID_class.large bns.elims finite_iff_le_card_var finite_ordLess_infinite2 insert_bound large_imp_infinite singl_bound)

local_setup \<open>MRBNF_Sugar.register_binder_sugar "Commitment.commit" {
  ctors = [
    (@{term Finp}, @{thm Finp_def}),
    (@{term Fout}, @{thm Fout_def}),
    (@{term Bout}, @{thm Bout_def}),
    (@{term Tau}, @{thm Tau_def}),
    (@{term Binp}, @{thm Binp_def}),
    (@{term Cmt}, @{thm refl})
  ],
  map_simps = [],
  distinct = [],
  bsetss = [[
    NONE,
    NONE,
    SOME @{term "\<lambda>x1 x2 x3. {x2}"},
    NONE,
    SOME @{term "\<lambda>x1 x2 x3. {x2}"},
    SOME @{term "\<lambda>x P. bns x"}
  ]],
  bset_bounds = @{thms bns_bound},
  strong_induct = @{thm refl},
  mrbnf = the (MRBNF_Def.mrbnf_of @{context} "Commitment.commit_pre"),
  set_simpss = [],
  subst_simps = NONE
}\<close>

abbreviation "swapa act x y \<equiv> map_action (id(x:=y,y:=x)) act"

lemma bvars_map_action[simp]: "bvars (map_action \<sigma> act) = image \<sigma> (bvars act)"
by (cases act, auto)

lemma rrename_commit_Cmt[simp]:
"bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>
 rrename_commit \<sigma> (Cmt act P) = Cmt (map_action \<sigma> act) (rrename \<sigma> P)"
by (cases act, auto)

lemma bvars_act_bout: "bvars act = {} \<or> (\<exists>a b. act = bout a b) \<or> (\<exists>a b. act = binp a b)"
by(cases act, auto)

lemma fra_eqvt[simp]: "fra (map_action \<sigma> act) = fra act"
  by (cases act) auto

lemma ns_map_action[simp]: "ns (map_action \<sigma> \<alpha>) = \<sigma> ` ns \<alpha>"
  by (cases \<alpha>) auto

end