theory Commitment
imports Pi  "Prelim.Curry_LFP" "Binders.Generic_Barendregt_Enhanced_Rule_Induction"
begin

binder_datatype 'var commit =
    Finp 'var 'var "'var term"
  | Fout 'var 'var "'var term"
  | Bout 'var x::'var "(t::'var) term" binds x in t
  | Tau "'var term"
  | Binp 'var x::'var "(t::'var) term" binds x in t

(* Monomorphization: *)
type_synonym cmt = "var commit"

lemmas toUnfold =
  UN_empty UN_empty2 UN_single Un_empty_left Un_empty_right
  comp_def empty_Diff
  map_prod_simp prod_set_simps
  map_sum.simps sum_set_simps prod_set_simps
  Sup_empty cSup_singleton
  (* *)
  Abs_commit_pre_inverse[OF UNIV_I]
  set1_commit_pre_def set2_commit_pre_def

lemmas commit_pre.map_id0[simp]
lemmas commit_pre_map_cong_id = commit_pre.map_cong[of _ _ _ id id id, simplified]

lemma Abs_commit_pre_inj[simp]: "Abs_commit_pre k = Abs_commit_pre k' \<longleftrightarrow> k = k'"
  by (metis toUnfold(21))

lemma Bout_inj[simp]: "Bout x y P = Bout x' y' P' \<longleftrightarrow> x = x' \<and> ((y' \<notin> FFVars P \<or> y' = y) \<and> P' = swap P y y')"
  unfolding Bout_def commit.TT_inject0 toUnfold map_commit_pre_def set3_commit_pre_def apply simp
  apply (rule iffI)
   apply (auto simp: id_on_def)[1]
   apply (rule term.permute_cong)
  apply auto
  subgoal apply(rule exI[of _ "(id(y:=y',y':=y))"])
    by (auto simp: id_on_def) .

lemma Binp_inj[simp]: "Binp x y P = Binp x' y' P' \<longleftrightarrow> x = x' \<and> ((y' \<notin> FFVars P \<or> y' = y) \<and> P' = swap P y y')"
unfolding Binp_def commit.TT_inject0 toUnfold map_commit_pre_def set3_commit_pre_def apply simp
  apply (rule iffI)
   apply (auto simp: id_on_def)[1]
   apply (rule term.permute_cong)
  apply auto
  subgoal apply(rule exI[of _ "(id(y:=y',y':=y))"])
    by (auto simp: id_on_def) .

(* Supply of fresh variables *)

lemma finite_FVars_commit: "finite (FVars_commit (C::var commit))"
  unfolding ls_UNIV_iff_finite[symmetric]
  by (rule commit.FVars_bd_UNIVs)

lemma exists_fresh:
"\<exists> z. z \<notin> set xs \<and> (\<forall>P \<in> set (Cs::var commit list). z \<notin> FVars_commit P)"
proof-
  have 0: "|set xs \<union> \<Union> (FVars_commit ` (set Cs))| <o |UNIV::var set|"
  unfolding ls_UNIV_iff_finite
  using finite_FVars_commit by blast
  then obtain x where "x \<notin> set xs \<union> \<Union> (FVars_commit ` (set Cs))"
    using MRBNF_FP.exists_fresh by blast
  thus ?thesis by auto
qed

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

lemma bns_bound: "|bns \<alpha>| <o |UNIV::'a::var set|"
  by (cases \<alpha>) (auto simp: emp_bound infinite_UNIV)

local_setup \<open>MRBNF_Sugar.register_binder_sugar "Commitment.commit" {
  ctors = [
    (@{term Finp}, @{thm Finp_def}),
    (@{term Fout}, @{thm Fout_def}),
    (@{term Bout}, @{thm Bout_def}),
    (@{term Tau}, @{thm Tau_def}),
    (@{term Binp}, @{thm Binp_def}),
    (@{term Cmt}, @{thm refl})
  ],
  permute_simps = @{thms commit.permute},
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
  strong_induct = NONE,
  inject = @{thms commit.inject},
  mrbnf = the (MRBNF_Def.mrbnf_of @{context} "Commitment.commit_pre"),
  set_simpss = [],
  subst_simps = NONE
}\<close>

abbreviation "swapa act x y \<equiv> map_action (id(x:=y,y:=x)) act"

lemma bvars_map_action[simp]: "bvars (map_action \<sigma> act) = image \<sigma> (bvars act)"
by (cases act, auto)

lemma permute_commit_Cmt[simp]:
"bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>
 permute_commit \<sigma> (Cmt act P) = Cmt (map_action \<sigma> act) (rrename \<sigma> P)"
by (cases act, auto)

lemma bvars_act_bout: "bvars act = {} \<or> (\<exists>a b. act = bout a b) \<or> (\<exists>a b. act = binp a b)"
by(cases act, auto)

lemma fra_eqvt[simp]: "fra (map_action \<sigma> act) = fra act"
  by (cases act) auto

lemma ns_map_action[simp]: "ns (map_action \<sigma> \<alpha>) = \<sigma> ` ns \<alpha>"
  by (cases \<alpha>) auto

end
