theory Commitment
imports Pi
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
  map_permute = @{thm commit.vvsubst_permute},
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
  subst_simps = NONE,
  IImsupp_Diffs = NONE,
  IImsupp_permute_commutes = NONE
}\<close>

abbreviation "swapa act x y \<equiv> map_action (id(x:=y,y:=x)) act"

lemma bvars_map_action[simp]: "bvars (map_action \<sigma> act) = image \<sigma> (bvars act)"
  by (cases act, auto)
lemma bvars_equiv[equiv]: "bij \<sigma> \<Longrightarrow> image \<sigma> (bvars act) = bvars (map_action \<sigma> act)"
  by simp

lemma permute_commit_Cmt[simp, equiv]:
"bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>
 permute_commit \<sigma> (Cmt act P) = Cmt (map_action \<sigma> act) (rrename \<sigma> P)"
by (cases act, auto)

lemma bvars_act_bout: "bvars act = {} \<or> (\<exists>a b. act = bout a b) \<or> (\<exists>a b. act = binp a b)"
by(cases act, auto)

lemma fra_eqvt[simp]: "fra (map_action \<sigma> act) = fra act"
  by (cases act) auto

lemma ns_map_action[simp]: "ns (map_action \<sigma> \<alpha>) = \<sigma> ` ns \<alpha>"
  by (cases \<alpha>) auto
lemma ns_equiv[equiv]: "bij \<sigma> \<Longrightarrow> \<sigma> ` ns \<alpha> = ns (map_action \<sigma> \<alpha>)"
  by simp

lemma Inp_inject: "(Inp x y e = Inp x' y' e') \<longleftrightarrow>
  x = x' \<and>
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FVars_term e - {y}) f \<and> f y = y' \<and> permute_term f e = e')"
  by (smt (z3) Abs_rrename Pi.supp_swap_bound Swapping.bij_swap id_onD id_on_swap swap_simps(1) term.inject(6))
lemma Res_inject: "(Res y e = Res y' e') \<longleftrightarrow>
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FVars_term e - {y}) f \<and> f y = y' \<and> permute_term f e = e')"
  by (smt (verit) Pi.supp_swap_bound Swapping.bij_swap id_onD id_on_swap swap_simps(1) term.inject(7) term.permute(8) term.permute_cong_id term.set(8))
lemma Bout_inject: "(Bout x y t = Bout x' y' t') \<longleftrightarrow>
  x = x' \<and>
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FVars_term t - {y}) f \<and> f y = y' \<and> permute_term f t = t')"
  by (smt (z3) Res_inject commit.inject(3) term.inject(7))
lemma Binp_inject: "(Binp x y t = Binp x' y' t') \<longleftrightarrow>
  x = x' \<and>
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FVars_term t - {y}) f \<and> f y = y' \<and> permute_term f t = t')"
  by (smt (z3) Res_inject commit.inject(5) term.inject(7))

lemmas commit.inject(3,5)[simp del]
lemmas term.inject(6,7)[simp del]

end
