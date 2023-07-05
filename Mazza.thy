theory Mazza
  imports
    Countably_Infinite_Set
    Countably_Infinite_Multiset
begin

(*untyped lambda calculus*)
(* binder_datatype 'a lam =
  Var 'a
| App "'a lam" "'a lam"
| Abs x::'a t::"'a lam" binds x in t
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ "'rec"}]),
  (("Abs", NONE), [@{typ "'bvar"}, @{typ 'brec}])
]

val spec_lam = {
  fp_b = @{binding "lam"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open> MRBNF_Sugar.create_binder_datatype spec_lam \<close>
print_mrbnfs

abbreviation "fv \<equiv> FFVars_lam"

(*infinitary untyped lambda calculus*)
(* binder_datatype 'a ilam =
  Bot
| Var 'a
| App "'a ilam" "'a ilam cinfmset"
| Abs "X::'a cinfset" "t::'a ilam" binds X in t
*)

ML \<open>
val ctors = [
  (("iVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("iApp", NONE), [@{typ 'rec}, @{typ "'rec cinfmset"}]),
  (("iAbs", NONE), [@{typ "'bvar cinfset"}, @{typ 'brec}])
]

val spec_ilam = {
  fp_b = @{binding "ilam"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding ivvsubst},
  tvsubst_b = @{binding itvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open> MRBNF_Sugar.create_binder_datatype spec_ilam \<close>
print_mrbnfs

lemma ex_inj_infinite_regular_var_ilam_pre:
  "\<exists>f :: 'a :: countable \<Rightarrow> 'b :: var_ilam_pre. inj f"
  unfolding card_of_ordLeq[of UNIV UNIV, simplified]
  apply (rule ordLeq_transitive[OF _ large])
  apply (rule ordLeq_transitive[OF countable_card_le_natLeq[THEN iffD1]])
  apply simp
  apply (rule natLeq_ordLeq_cinfinite)
  apply (rule ilam_pre.bd_Cinfinite)
  done

definition embed :: "'a :: countable \<Rightarrow> 'b :: var_ilam_pre"
  ("{{_}}" [999] 1000)  where
  "embed = (SOME f. inj f)"

lemma inj_embed: "inj embed"
  unfolding embed_def
  by (rule someI_ex[OF ex_inj_infinite_regular_var_ilam_pre[where 'a='a]])

abbreviation "ifv \<equiv> FFVars_ilam"

consts lam_ilam :: "'b :: var_ilam_pre lam \<Rightarrow> nat list \<Rightarrow> 'b :: var_ilam_pre ilam"  ("\<lbrakk>_\<rbrakk>_" [999, 1000] 1000)
consts ilam_lam :: "'b :: var_ilam_pre ilam \<Rightarrow> 'b :: var_ilam_pre lam"  ("\<lparr>_\<rparr>" [999] 1000)

lemma iso_partition_into_countable: "|UNIV :: 'a :: var_ilam_pre set| *c natLeq =o |UNIV :: 'a :: var_ilam_pre set|"
  by (rule cprod_infinite1'[OF _ Cinfinite_Cnotzero[OF natLeq_Cinfinite]])
    (simp_all add: var_ilam_pre_class.cinfinite var_sum_class.large)


definition iso_partition where
  "iso_partition = (SOME f:: 'a :: var_ilam_pre \<Rightarrow> nat \<Rightarrow> 'a. bij_betw (case_prod f) UNIV UNIV)"

lemma bij_iso_partition: "bij (case_prod iso_partition :: 'a::var_ilam_pre \<times> nat \<Rightarrow> 'a)"
  unfolding iso_partition_def using iso_partition_into_countable[where 'a='a]
  unfolding cprod_def Field_card_of Field_natLeq card_of_ordIso[symmetric] UNIV_prod[symmetric]
  by (elim exE someI[where P = "\<lambda>f. bij (case_prod f)" and x="\<lambda>x y. _ (x, y)", simplified])

definition var_partition where
  "var_partition = range (\<lambda>v :: 'a :: var_ilam_pre. range (iso_partition v))"

lemma partition_var_partition: "partition_on UNIV var_partition"
  unfolding partition_on_def disjoint_def var_partition_def
  using bij_iso_partition unfolding bij_def surj_def inj_on_def
  by (auto 5 5)

lemma inj_iso_partition: "inj (iso_partition X)"
  using bij_iso_partition unfolding bij_def inj_on_def
  by auto

lemma var_partition_cinf: "X \<in> var_partition \<Longrightarrow> countable X \<and> infinite X"
  unfolding var_partition_def
  by (auto intro!: range_inj_infinite[OF inj_iso_partition])

lemma ex1_var_partition: "\<exists>!X. X \<in> var_partition \<and> x \<in> X"
  using partition_var_partition unfolding partition_on_def disjoint_def by auto

lift_definition super :: "'a ::var_ilam_pre \<Rightarrow> 'a cinfset" ("\<lbrace>_\<rbrace>" [999] 1000) is
  "\<lambda>x. THE X. X \<in> var_partition \<and> x \<in> X"
  by (rule the1I2[OF ex1_var_partition]) (auto simp: var_partition_cinf)

lemma in_super: "x \<in>\<in> \<lbrace>x\<rbrace>"
  by transfer (rule the1I2[OF ex1_var_partition, THEN conjunct2])

lemma super_in: "set_cinfset \<lbrace>x\<rbrace> \<in> var_partition"
  by transfer (rule the1I2[OF ex1_var_partition, THEN conjunct1])

lemma disjoint_super: "\<lbrace>x\<rbrace> \<noteq> \<lbrace>y\<rbrace> \<Longrightarrow> set_cinfset \<lbrace>x\<rbrace> \<inter> set_cinfset \<lbrace>y\<rbrace> = {}"
  by (metis Int_emptyI ex1_var_partition set_cinfset_inject super_in)

typedef 'a PP_lam_ilam = "UNIV :: nat list set" by blast
setup_lifting type_definition_PP_lam_ilam
lift_definition myCons :: "nat \<Rightarrow> 'a PP_lam_ilam \<Rightarrow> 'a PP_lam_ilam" is Cons .
type_synonym 'a UU_lam_ilam = "'a ilam"
type_synonym 'a PPUU_lam_ilam = "'a PP_lam_ilam \<Rightarrow> 'a UU_lam_ilam"

subclass (in var_ilam_pre) var_lam_pre
  by standard

definition CCCTOR_lam_ilam :: "('a::var_ilam_pre, 'a, 'a lam \<times> 'a PPUU_lam_ilam, 'a lam \<times> 'a PPUU_lam_ilam) lam_pre \<Rightarrow> 'a PPUU_lam_ilam" where
  "CCCTOR_lam_ilam lp = (\<lambda>a. case Rep_lam_pre lp of
     Inl x \<Rightarrow> iVar (get_cinfset \<lbrace>x\<rbrace> (list_encode (Rep_PP_lam_ilam a)))
   | Inr (Inl (M, N)) \<Rightarrow> iApp (snd M (myCons 0 a)) (image_cinfmset (\<lambda>i. snd N (myCons (i + 1) a)) NATS_cinfmset)
   | Inr (Inr (x, M)) \<Rightarrow> iAbs \<lbrace>x\<rbrace> (snd M a))"

ML_file \<open>Tools/mrbnf_recursor2.ML\<close>

ML \<open>Multithreading.parallel_proofs := 0\<close>

local_setup \<open>fn lthy =>
let
  fun rtac ctxt = resolve_tac ctxt o single
  val model_tacs = {
    small_avoiding_sets = [fn ctxt => print_tac ctxt "small" THEN Skip_Proof.cheat_tac ctxt 1],
    Umap_id0 = fn ctxt => print_tac ctxt "Umap_id" THEN Skip_Proof.cheat_tac ctxt 1,
    Umap_comp0 = fn ctxt => print_tac ctxt "Umap_comp" THEN Skip_Proof.cheat_tac ctxt 1,
    Umap_cong_id = fn ctxt => print_tac ctxt "Umap_cong_id" THEN Skip_Proof.cheat_tac ctxt 1,
    UFVars_Umap = [fn ctxt => print_tac ctxt "UFVars_Umap" THEN Skip_Proof.cheat_tac ctxt 1],
    Umap_Uctor = fn ctxt => print_tac ctxt "Umap_Uctor" THEN Skip_Proof.cheat_tac ctxt 1,
    UFVars_subsets = [fn ctxt => print_tac ctxt "UFVars_subset" THEN Skip_Proof.cheat_tac ctxt 1]
  } : (Proof.context -> tactic) MRBNF_Recursor.model_axioms;

  val params = {
    P = @{typ "('a :: var_ilam_pre) PP_lam_ilam"},
    PFVarss = [@{term "\<lambda>_ :: 'a PP_lam_ilam. {} :: 'a :: var_ilam_pre set"}],
    Pmap = @{term "\<lambda>(_ :: 'a \<Rightarrow> 'a). id :: 'a :: var_ilam_pre PP_lam_ilam \<Rightarrow> 'a PP_lam_ilam"},
    axioms = {
      Pmap_id0 = fn ctxt => print_tac ctxt "Pmap_id" THEN Skip_Proof.cheat_tac ctxt 1,
      Pmap_comp0 = fn ctxt => print_tac ctxt "Pmap_comp" THEN Skip_Proof.cheat_tac ctxt 1,
      Pmap_cong_id = fn ctxt => print_tac ctxt "Pmap_cong_id" THEN Skip_Proof.cheat_tac ctxt 1,
      PFVars_Pmaps = [fn ctxt => print_tac ctxt "PFVars_Pmaps" THEN Skip_Proof.cheat_tac ctxt 1],
      small_PFVarss = [fn ctxt => print_tac ctxt "small_PFVars" THEN Skip_Proof.cheat_tac ctxt 1]
    },
    min_bound = false
  } : (Proof.context -> tactic) MRBNF_Recursor.parameter;

  val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of lthy @{type_name lam});
  val model = {
    U = @{typ "'a :: var_ilam_pre ilam"},
    fp_result = fp_res,
    UFVars = [@{term "(\<lambda>u t. FFVars_ilam u) :: 'a ilam \<Rightarrow> 'a ilam \<Rightarrow> 'a :: var_ilam_pre set"}],
    Umap = @{term "(\<lambda>f u t. ivvsubst f u) :: ('a \<Rightarrow> 'a) \<Rightarrow> 'a ilam \<Rightarrow> 'a ilam \<Rightarrow> 'a :: var_ilam_pre ilam"},
    Uctor = @{term CCCTOR_lam_ilam},
    avoiding_sets = [ @{term "{} :: 'a::var_ilam_pre set"}],
    parameters = params,
    axioms = model_tacs
  } : (Proof.context -> tactic) MRBNF_Recursor.model;
  val _ = model;
  val (res, lthy) = MRBNF_Recursor2.create_binding_recursor (Binding.suffix_name "_lam_ilam") model (Binding.name "lam_ilam") lthy;
  val notes = [
    ("ctor", [#rec_Uctor res]),
    ("swap", [#rec_swap res]),
    ("ifv", #rec_UFVarss res)
  ] |> (map (fn (thmN, thms) =>
      ((Binding.qualify true "lam_ilam" (Binding.name thmN), []), [(thms, [])])
      ));
  val (_, lthy) = Local_Theory.notes notes lthy;
in lthy end
\<close>

print_theorems
find_theorems name: swap name: Mazza

lemma lam_ilam_simps[simp]:
  "\<lbrakk>Var x\<rbrakk>a = iVar (get_cinfset \<lbrace>x\<rbrace> (list_encode a))"
  "\<lbrakk>Abs x M\<rbrakk>a = iAbs \<lbrace>x\<rbrace> (\<lbrakk>M\<rbrakk>a)"
  "\<lbrakk>App M N\<rbrakk>a = iApp \<lbrakk>M\<rbrakk>(0#a) (image_cinfmset (\<lambda>i. \<lbrakk>N\<rbrakk>((i + 1) # a)) NATS_cinfmset)"
  sorry

lemma ifv_lam_ilam_disjoint:
  fixes M N :: "'a :: var_ilam_pre lam"
  assumes "\<not>a \<le> a'" "\<not>a' \<le> a"
  shows "ifv (\<lbrakk>M\<rbrakk>a) \<inter> ifv (\<lbrakk>N\<rbrakk>a') = {}"
  sorry

inductive affine where
  "affine (iVar x)"
| "affine t \<Longrightarrow> affine (iAbs xx t)"
| "affine t \<Longrightarrow>
   \<forall>u. u \<in>#\<in> uu \<longrightarrow> affine u \<and> ifv t \<inter> ifv u = {} \<Longrightarrow>
   \<forall>u u'. u \<in>#\<in> uu \<longrightarrow> u' \<in>#\<in> uu \<longrightarrow> u \<noteq> u' \<longrightarrow> ifv u \<inter> ifv u' = {} \<Longrightarrow>
   affine (iApp t uu)"

lemma
  fixes M :: "'a :: var_ilam_pre lam"
  shows "affine (\<lbrakk>M\<rbrakk>a)"
  by (induct M arbitrary: a)
    (auto simp: cinfmset.set_map intro!: affine.intros
      elim: ifv_lam_ilam_disjoint[unfolded disjoint_iff, rule_format, THEN notE, of _ _ _ _ _ False, rotated 2])+


inductive uniform where
  "uniform (iVar x)"
| "uniform t \<Longrightarrow> uniform (iAbs \<lbrace>xx\<rbrace> t)"
| "uniform t \<Longrightarrow> \<forall>u. u \<in>#\<in> uu \<longrightarrow> uniform u \<Longrightarrow>
   \<forall>u u'. u \<in>#\<in> uu \<longrightarrow> u' \<in>#\<in> uu \<longrightarrow> u \<noteq> u' \<longrightarrow>
   u = u' \<Longrightarrow>
   uniform (iApp t uu)"

end
