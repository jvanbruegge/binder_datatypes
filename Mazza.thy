theory Mazza
  imports
    "thys/MRBNF_Recursor"
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

(*
typedef 'a :: var_ilam_pre super =
   "{f :: 'a \<Rightarrow> 'a cinfset. \<forall>x y. x \<in>\<in> f x \<and>
       (f x \<noteq> f y \<longrightarrow> set_cinfset (f x) \<inter> set_cinfset (f y) = {})}"
  by (auto intro!: exI[of _ super] simp: in_super dest: disjoint_super)
setup_lifting type_definition_super
lift_definition apply_super :: "'a :: var_ilam_pre super \<Rightarrow> 'a \<Rightarrow> 'a cinfset" is "id :: _ \<Rightarrow> ('a \<Rightarrow> 'a cinfset)" .
lift_definition comp_super :: "'a :: var_ilam_pre super \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a :: var_ilam_pre super" is
  "\<lambda>g f. if bij f then g o f else g"
  apply auto
  subgoal for f g x
    sledgehammer
  sorry
*)

definition bij_cinfset where
  "bij_cinfset A B x = (if x \<in>\<in> A then get_cinfset B (idx_cinfset A x) else x)"

lemma bij_cinfset: "bij_betw (bij_cinfset A B) (set_cinfset A) (set_cinfset B)"
  unfolding bij_cinfset_def
  apply transfer
  subgoal for A B
    apply (intro bij_betwI')
      apply (auto simp: bij_betw_def image_iff intro!: inj_onI from_nat_into) [2]
    subgoal for y
      apply (rule bexI[of _ "from_nat_into A (to_nat_on B y)"])
       apply (auto intro: from_nat_into)
      done
    done
  done

lemma card_of_set_cinfset: "|set_cinfset A| =o natLeq"
  using bij_betw_idx_cinfset card_of_nat card_of_ordIso ordIso_transitive by blast

lemma supp_bij_cinfset[simp]:
  "|supp (bij_cinfset A B :: 'a \<Rightarrow> 'a)| <o |UNIV :: 'a :: var_ilam_pre set|"
  unfolding bij_cinfset_def supp_def
  apply (rule ordLeq_ordLess_trans[of _ "|set_cinfset A|", OF card_of_mono1])
   apply (auto intro!: ordIso_ordLess_trans[OF card_of_set_cinfset])
  sorry

lemma
  fixes z0
  defines "T \<equiv> (\<lambda>g a. iVar (get_cinfset (g z0) (list_encode a)))"
  shows "\<forall>z Z g a. T (g(z := Z)) a = ivvsubst (bij_cinfset (g z) Z) (T g a)"
  apply (auto simp: T_def)
   apply (auto simp: bij_cinfset_def get_cinfset_in get_cinfset_inverse)
  sorry

typedef 'a P_lam_ilam = "UNIV :: unit set" by auto
typedef 'a :: var_ilam_pre U_lam_ilam = "{T :: ('a \<Rightarrow> 'a cinfset) \<Rightarrow> nat list \<Rightarrow> 'a ilam.
  \<forall>z Z g a. T (g(z := Z)) a = ivvsubst (bij_cinfset (g z) Z) (T g a)}"
  apply (rule exI[of _ "\<lambda>g a. iVar (get_cinfset (g undefined) (list_encode a))"] CollectI allI)+
  apply (auto simp: bij_cinfset_def get_cinfset_in get_cinfset_inverse)
  subgoal for z Z g a
    apply (cases "g undefined = g z")
     apply (auto simp: bij_cinfset_def get_cinfset_in get_cinfset_inverse)
    defer
    sledgehammer
  apply (simp add: bij_cinfset_def get_cinfset_in get_cinfset_inverse)
  find_theorems ivvsubst iVar
type_synonym 'a PU_lam_ilam = "'a P_lam_ilam \<Rightarrow> 'a U_lam_ilam"

subclass (in var_ilam_pre) var_lam_pre
  by standard

definition CCTOR_lam_ilam :: "('a::var_ilam_pre, 'a, 'a lam \<times> 'a PU_lam_ilam, 'a lam \<times> 'a PU_lam_ilam) lam_pre \<Rightarrow> 'a PU_lam_ilam" where
  "CCTOR_lam_ilam lp = (\<lambda>u. case Rep_lam_pre lp of
     Inl x \<Rightarrow> \<lambda>g a. iVar (get_cinfset (apply_super g x) (list_encode a))
   | Inr (Inl (M, N)) \<Rightarrow> \<lambda>g a. iApp (snd M u g (0 # a)) (image_cinfmset (\<lambda>i. snd N u g ((i + 1) # a)) \<nat>#)
   | Inr (Inr (x, M)) \<Rightarrow> \<lambda>g a. iAbs (apply_super g x) (snd M u g a))"

lemma apply_super_comp_super[simp]: "apply_super (comp_super g f) x = apply_super g (f x)"
  apply transfer
  apply auto
  done

lemma map_CCTOR_lam_ilam:
  "bij f \<Longrightarrow>
       |supp (f :: 'a \<Rightarrow> 'a)| <o |UNIV :: 'a :: var_ilam_pre set| \<Longrightarrow>
       (\<lambda>g. CCTOR_lam_ilam y p (comp_super g f)) =
       CCTOR_lam_ilam
        (map_lam_pre f f
          (\<lambda>(t, pu). (rrename_lam f t, \<lambda>p g. pu (id p) (comp_super g f)))
          (\<lambda>(t, pu). (rrename_lam f t, \<lambda>p g. pu (id p) (comp_super g f))) y)
        (id p) "
  apply (auto simp: CCTOR_lam_ilam_def map_lam_pre_def Abs_lam_pre_inverse
    cinfmset.map_comp o_def split: sum.splits prod.splits)
  done

definition "AbsT z T = (\<lambda>g a. iAbs (apply_super g z) (T g a))"

definition "fvT T = {x. \<exists>g g'.
           (\<exists>a. T g a \<noteq> T g' a) \<and>
           (\<forall>y. y \<noteq> x \<longrightarrow> apply_super g y = apply_super g' y)}"

lemma "fvT (AbsT z T) \<subseteq> fvT T - {z}"
  unfolding AbsT_def fvT_def
  apply auto
  subgoal sorry
  subgoal for g g' a
    apply (erule notE)
    apply (cases "g = g'")
    apply auto

lemma set_CCTOR_lam_ilam: "set2_lam_pre y \<inter> ({} \<union> {}) = {} \<Longrightarrow>
       (\<And>t pu p.
           (t, pu) \<in> set3_lam_pre y \<union> set4_lam_pre y \<Longrightarrow>
           {x. \<exists>g g' a. pu p g a \<noteq> pu p g' a \<and> (\<forall>y. y \<noteq> x \<longrightarrow> apply_super g y = apply_super g' y)}
           \<subseteq> fv t \<union> {} \<union> {}) \<Longrightarrow>
       {x. \<exists>g g' a.
              CCTOR_lam_ilam y p g a \<noteq> CCTOR_lam_ilam y p g' a \<and> (\<forall>y. y \<noteq> x \<longrightarrow> apply_super g y = apply_super g' y)}
       \<subseteq> fv (lam_ctor (map_lam_pre id id fst fst y)) \<union> {} \<union> {}"
  apply (auto simp: CCTOR_lam_ilam_def
    Var_def[symmetric] Abs_def[symmetric] App_def[symmetric]
    map_lam_pre_def set3_lam_pre_def set4_lam_pre_def

 split: sum.splits prod.splits)
     apply metis
  subgoal
  apply (erule contrapos_np) sorry
   apply (erule contrapos_np)
  subgoal for y t rec x g g' a
    apply (drule meta_spec[of _ t])
    apply (drule meta_spec[of _ p])
    apply simp
    apply (cases "x \<noteq> y")
     apply simp
     apply (smt (verit) mem_Collect_eq subsetD)
    apply simp
    apply (cases "rec p g a = rec p g' a")
    apply (drule subsetD[of _ _ y])
     apply auto
    apply (rule exI[of _ g])
    apply (rule exI[of _ g'])
    apply auto
    sorry
   apply (erule contrapos_np)
  subgoal for y t rec g g' a
    apply (drule meta_spec[of _ t])
    apply (drule meta_spec[of _ p])
    apply simp


local_setup \<open>fn lthy =>
let
  fun rtac ctxt = resolve_tac ctxt o single
  val model_tacs = {
    small_avoiding_sets = [fn ctxt => rtac ctxt @{thm emp_bound} 1],
    Umap_id0 = fn ctxt => rtac ctxt @{thm ilam.map_id0} 1,
    Umap_comp0 = fn ctxt => (rtac ctxt @{thm ilam.map_comp0} THEN_ALL_NEW assume_tac ctxt) 1,
    Umap_cong_id = fn ctxt => (rtac ctxt @{thm trans[OF ilam.map_cong[OF _ supp_id_bound refl] ilam.map_id, simplified]}
       THEN_ALL_NEW FIRST' [assume_tac ctxt, Goal.assume_rule_tac ctxt]) 1,
    UFVars_Umap = [fn ctxt => rtac ctxt @{thm ilam.set_map} 1 THEN assume_tac ctxt 1],
    Umap_Uctor = fn ctxt => print_tac ctxt "map" THEN Skip_Proof.cheat_tac ctxt 1 (*(rtac ctxt @{thm map_CCTOR_lam_ilam} THEN_ALL_NEW assume_tac ctxt) 1*),
    UFVars_subsets = [fn ctxt => print_tac ctxt "set" THEN Skip_Proof.cheat_tac ctxt (*(rtac ctxt @{thm set_CCTOR_lam_ilam}
       THEN_ALL_NEW FIRST' [assume_tac ctxt, Goal.assume_rule_tac ctxt])*) 1]
  } : (Proof.context -> tactic) MRBNF_Recursor.model_axioms;

  val params = {
    P = @{typ "('a :: var_ilam_pre) P_lam_ilam"},
    PFVarss = [@{term "\<lambda>_ :: 'a P_lam_ilam. {} :: 'a :: var_ilam_pre set"}],
    Pmap = @{term "\<lambda>(_ :: 'a \<Rightarrow> 'a). id :: 'a :: var_ilam_pre P_lam_ilam \<Rightarrow> 'a P_lam_ilam"},
    axioms = {
      Pmap_id0 = fn ctxt => rtac ctxt refl 1,
      Pmap_comp0 = fn ctxt => rtac ctxt sym 1 THEN rtac ctxt @{thm id_o} 1,
      Pmap_cong_id = fn ctxt => rtac ctxt @{thm id_apply} 1,
      PFVars_Pmaps = [fn ctxt => rtac ctxt sym 1 THEN rtac ctxt @{thm image_empty} 1],
      small_PFVarss = [fn ctxt => rtac ctxt @{thm emp_bound} 1]
    },
    min_bound = false
  } : (Proof.context -> tactic) MRBNF_Recursor.parameter;

  val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of lthy @{type_name lam});
  val model = {
    U = @{typ "'a :: var_ilam_pre U_lam_ilam"},
    fp_result = fp_res,
    UFVars = [@{term "(\<lambda>t T. {x. \<exists>g g' a. T g a \<noteq> T g' a \<and> (\<forall>y. y \<noteq> x \<longrightarrow> apply_super g y = apply_super g' y)}) :: 'a lam \<Rightarrow> 'a U_lam_ilam \<Rightarrow> 'a :: var_ilam_pre set"}],
    Umap = @{term "(\<lambda>f t T g a. T (comp_super g f) a) :: ('a \<Rightarrow> 'a) \<Rightarrow> 'a lam \<Rightarrow> 'a U_lam_ilam \<Rightarrow> 'a :: var_ilam_pre U_lam_ilam"},
    Uctor = @{term CCTOR_lam_ilam},
    avoiding_sets = [ @{term "{} :: 'a::var_ilam_pre set"}],
    parameters = params,
    axioms = model_tacs
  } : (Proof.context -> tactic) MRBNF_Recursor.model;
  val _ = model;
  val (res, lthy) = MRBNF_Recursor.create_binding_recursor (Binding.qualify false "lam_ilam") model (Binding.name "lam_ilam") lthy;
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



lemma
  "f g (Var x :: 'a :: var_ilam_pre lam) a = (iVar (get_cinfset (g x) (list_encode a)) :: 'a ilam)"
  "f g (Abs x M) a = iAbs (g x) (f g M a)"
  "f g (App M N) a = iApp (f g M (0#a)) (image_cinfmset (\<lambda>i. f g N ((i + 1) # a)) \<nat>#)"
  sorry

abbreviation lam_ilam ("\<lbrakk>_\<rbrakk>_" [999, 1000] 1000) where "lam_ilam t xs \<equiv> ff0_lam_ilam t (Abs_P_lam_ilam xs)"

lemma lam_ilam_simps[simp]:
  "\<lbrakk>Var x\<rbrakk>a = iVar (get_cinfset \<lbrace>x\<rbrace> (list_encode a))"
  "\<lbrakk>Abs x M\<rbrakk>a = iAbs \<lbrace>x\<rbrace> (\<lbrakk>M\<rbrakk>a)"
  "\<lbrakk>App M N\<rbrakk>a = iApp \<lbrakk>M\<rbrakk>(0#a) (image_cinfmset (\<lambda>i. \<lbrakk>N\<rbrakk>((i + 1) # a)) \<nat>#)"
  unfolding Var_def Abs_def App_def
    apply (subst lam_ilam.ctor; auto simp: noclash_lam_def set1_lam_pre_def set2_lam_pre_def map_lam_pre_def
      Abs_lam_pre_inverse Abs_P_lam_ilam_inverse
      CCTOR_lam_ilam_def split: sum.splits)
   apply (subst lam_ilam.ctor; auto simp: noclash_lam_def set1_lam_pre_def set4_lam_pre_def map_lam_pre_def
      Abs_lam_pre_inverse Abs_P_lam_ilam_inverse
      CCTOR_lam_ilam_def split: sum.splits)
  apply (subst lam_ilam.ctor; auto simp: noclash_lam_def set2_lam_pre_def set4_lam_pre_def map_lam_pre_def
      Abs_lam_pre_inverse Abs_P_lam_ilam_inverse myCons.abs_eq
      CCTOR_lam_ilam_def split: sum.splits)
  done

context includes cinfmset.lifting begin

lemma in_image_cinfmset: "y \<in>#\<in> image_cinfmset f X \<longleftrightarrow> y \<in> f ` set_cinfmset X"
  apply transfer
  apply (auto simp: Let_def image_iff)
   apply (metis (mono_tags, lifting) disjoint_iff_not_equal finite.emptyI mem_Collect_eq vimage_singleton_eq)+
  done

lemma NATS_cinfmset_UNIV: "i \<in>#\<in> \<nat>#"
  by transfer auto

end

thm lam_ilam.ifv

lemma ifv_subset: "ifv (\<lbrakk>M\<rbrakk>a) \<subseteq> {x. \<exists>y b. y \<in> fv M \<and> rev a \<le> rev b \<and> x = get_cinfset \<lbrace>y\<rbrace> (list_encode b)}"
  apply (induct M arbitrary: a)
    apply (auto simp: in_image_cinfmset NATS_cinfmset_UNIV)
    apply (smt (verit, ccfv_threshold) Prefix_Order.prefixI dual_order.trans in_mono mem_Collect_eq rev.simps(2))
   apply (smt (verit, ccfv_threshold) Prefix_Order.prefixI dual_order.trans in_mono mem_Collect_eq rev.simps(2))
  using get_cinfset_in by blast

lemma ifv_lam_ilam_disjoint:
  fixes M N :: "'a :: var_ilam_pre lam"
  assumes "\<not>rev a \<le> rev a'" "\<not>rev a' \<le> rev a"
  shows "ifv (\<lbrakk>M\<rbrakk>a) \<inter> ifv (\<lbrakk>N\<rbrakk>a') = {}"
  apply (auto dest!: set_mp[OF ifv_subset])
  subgoal for x y b b'
    apply (subgoal_tac "\<lbrace>x\<rbrace> = \<lbrace>y\<rbrace>")
    subgoal
      apply simp
      apply (drule injD[OF inj_get_cinfset])
      apply (drule injD[OF inj_list_encode])
      apply (smt (verit, ccfv_SIG) Prefix_Order.prefixE Prefix_Order.prefixI append_eq_append_conv2 assms(1) assms(2))
      done
    apply (metis IntI disjoint_super emptyE get_cinfset_in)
    done
  done

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


consts ilam_lam :: "'b :: var_ilam_pre ilam \<Rightarrow> 'b :: var_ilam_pre lam"  ("\<lparr>_\<rparr>" [999] 1000)

inductive uniform where
  "uniform (iVar x)"
| "uniform t \<Longrightarrow> uniform (iAbs \<lbrace>xx\<rbrace> t)"
| "uniform t \<Longrightarrow> \<forall>u. u \<in>#\<in> uu \<longrightarrow> uniform u \<Longrightarrow>
   \<forall>u u'. u \<in>#\<in> uu \<longrightarrow> u' \<in>#\<in> uu \<longrightarrow> u \<noteq> u' \<longrightarrow>
   u = u' \<Longrightarrow>
   uniform (iApp t uu)"

end
