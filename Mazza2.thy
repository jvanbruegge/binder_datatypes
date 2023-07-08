theory Mazza2
  imports
    "thys/MRBNF_Recursor"
    "HOL-Library.Stream"
    "HOL-Library.Countable_Set_Type"
    "HOL-Cardinals.Cardinals"
begin

class infinite_regular =
  assumes large: "|Field (card_suc natLeq)| \<le>o |UNIV::'a set|" and regular: "regularCard |UNIV::'a set|"

lemma infinite_natLeq: "natLeq \<le>o |A| \<Longrightarrow> infinite A"
  using infinite_iff_natLeq_ordLeq by blast

lemma infinite: "infinite (UNIV :: 'a ::infinite_regular set)"
  using ordLeq_transitive[OF ordLess_imp_ordLeq[OF card_suc_greater_set[OF natLeq_card_order ordLeq_refl[OF natLeq_Card_order]]]
      ordIso_ordLeq_trans[OF ordIso_symmetric[OF card_of_Field_ordIso[OF Card_order_card_suc[OF natLeq_card_order]]] large]]
  by (rule infinite_natLeq)

lemma infinite_ex_inj: "\<exists>f :: nat \<Rightarrow> 'a :: infinite_regular. inj f"
  by (rule infinite_countable_subset[OF infinite, simplified])

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

coinductive sdistinct where
  "x \<notin> sset s \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (x ## s)"

lemma sdistinct_stl: "sdistinct s \<Longrightarrow> sdistinct (stl s)"
  by (erule sdistinct.cases) simp

lemma sdistinct_fromN[simp]: "sdistinct (fromN n)"
  by (coinduction arbitrary: n) (subst siterate.code,  auto)

lemma sdistinct_smap: "inj_on f (sset s) \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (smap f s)"
  by (coinduction arbitrary: s)
    (auto simp: smap_ctr stream.set_map inj_on_def stream.set_sel sdistinct_stl elim: sdistinct.cases)

typedef 'a dstream = "{xs :: 'a :: infinite_regular stream. sdistinct xs}"
  by (auto intro!: exI[of _ "smap (SOME f :: nat \<Rightarrow> 'a. inj f) nats"] sdistinct_smap
    someI_ex[OF infinite_ex_inj])

setup_lifting type_definition_dstream

lift_definition map_dstream :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dstream \<Rightarrow> 'a :: infinite_regular dstream" is
  "\<lambda>f xs. if bij f then smap f xs else xs"
  by (auto simp: bij_def intro!: sdistinct_smap elim: inj_on_subset)

lift_definition set_dstream :: "'a :: infinite_regular dstream \<Rightarrow> 'a set" is "sset" .

mrbnf "'a ::infinite_regular dstream"
  map: map_dstream
  sets: bound: set_dstream
  bd: natLeq
  var_class: infinite_regular
  subgoal apply (rule ext, transfer)
    using [[show_consts]]
    apply simp
(*
  subgoal by (rule ext, transfer) simp
  subgoal by transfer simp
  subgoal by (rule ext, transfer) simp
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by transfer (simp flip: finite_iff_ordLess_natLeq)
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done
*)
*)

declare [[mrbnf_internals]]
local_setup \<open> MRBNF_Sugar.create_binder_datatype spec_lam \<close>
print_mrbnfs

abbreviation "fv \<equiv> FFVars_lam"

(*infinitary untyped lambda calculus*)
(* binder_datatype 'a ilam =
  Bot
| Var 'a
| App "'a ilam" "'a ilam stream"
| Abs "X::'a dstream" "t::'a ilam" binds X in t
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

typedef 'a :: var_ilam_pre super =
   "{f :: 'a \<Rightarrow> 'a cinfset. \<forall>x y. f x \<noteq> f y \<longrightarrow> set_cinfset (f x) \<inter> set_cinfset (f y) = {}}"
  by (auto intro!: exI[of _ super] simp: in_super dest: disjoint_super)
setup_lifting type_definition_super
lift_definition apply_super :: "'a :: var_ilam_pre super \<Rightarrow> 'a \<Rightarrow> 'a cinfset" is "id :: _ \<Rightarrow> ('a \<Rightarrow> 'a cinfset)" .
lift_definition comp_super :: "'a :: var_ilam_pre super \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a :: var_ilam_pre super" is
  "\<lambda>g f. if bij f then g o f else g"
  by force
lift_definition swap_super :: "'a :: var_ilam_pre super \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a :: var_ilam_pre super" is
  "\<lambda>g z z'. g (z := g z', z' := g z)"
  by (auto split: if_splits)

lemma apply_super_disjoint:
  "x \<in>\<in> apply_super g z \<Longrightarrow> x \<in>\<in> apply_super g z' \<Longrightarrow> apply_super g z = apply_super g z'"
  by transfer auto

lemma apply_super_swap_super[simp]: "apply_super (swap_super g z z') x =
  (if x = z then apply_super g z' else if x = z' then apply_super g z else apply_super g x)"
  apply transfer
  apply auto
  done

definition bij_cinfset where
  "bij_cinfset A B x = (if x \<in>\<in> A then get_cinfset B (idx_cinfset A x)
     else if x \<in>\<in> B then get_cinfset A (idx_cinfset B x)
     else x)"

lemma bij_betw_cinfset: "bij_betw (bij_cinfset A B) (set_cinfset A) (set_cinfset B)"
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

lemma bij_cinfset: "set_cinfset A \<inter> set_cinfset B = {} \<Longrightarrow> bij (bij_cinfset A B)"
  unfolding bij_def inj_def surj_def bij_cinfset_def
  apply transfer
  apply (auto simp: image_iff)
        apply (metis Int_emptyD finite.emptyI from_nat_into)
       apply (metis finite.emptyI from_nat_into)
      apply (metis Int_emptyD finite.emptyI from_nat_into)
     apply (metis finite.emptyI from_nat_into)
    apply (metis finite.emptyI from_nat_into)
   apply (metis finite.emptyI from_nat_into)
  apply (metis Int_emptyD finite.emptyI from_nat_into from_nat_into_to_nat_on to_nat_on_from_nat_into_infinite)
  done

lemma card_of_set_cinfset: "|set_cinfset A| =o natLeq"
  using bij_betw_idx_cinfset card_of_nat card_of_ordIso ordIso_transitive by blast

subclass (in var_ilam_pre) var_lam_pre
  by standard

lemma set_cinfset_bound: "|set_cinfset A :: 'a set| <o |UNIV :: 'a :: var_ilam_pre set|"
  apply (rule ordIso_ordLess_trans[OF card_of_set_cinfset])
  apply (rule ordLess_ordLeq_trans[OF _ ilam.var_large])
  apply (rule ordLess_ordIso_trans[OF card_suc_greater[OF natLeq_card_order]])
  apply (tactic \<open>BNF_Tactics.unfold_thms_tac @{context} [Thm.axiom @{theory} "Mazza.ilam_pre.bd_ilam_pre_def"]\<close>)
  apply (rule ordIso_transitive[OF _ dir_image_ordIso])
    apply (rule ordIso_symmetric)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Cinfinite_csum Field_natLeq natLeq_card_order natLeq_cinfinite)
      apply (simp add: lam_pre.bd_Cnotzero)
     apply (simp add: Field_natLeq natLeq_card_order ordLeq_csum1)
    apply (rule ordIso_transitive)
     apply (rule csum_absorb2)
      apply (simp add: Card_order_cprod Cinfinite_csum1 cinfinite_cprod natLeq_Cinfinite)
     apply (simp add: Card_order_cprod Cinfinite_csum1 cinfinite_cprod natLeq_Cinfinite natLeq_ordLeq_cinfinite)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Card_order_csum cinfinite_cprod cinfinite_csum natLeq_Cinfinite)
      apply (simp add: lam_pre.bd_Cnotzero)
     apply (simp add: Card_order_csum cinfinite_cprod cinfinite_csum natLeq_Cinfinite natLeq_ordLeq_cinfinite)
    apply (rule ordIso_transitive)
     apply (rule csum_absorb2)
      apply (simp add: Card_order_cprod cinfinite_cprod cinfinite_csum natLeq_Cinfinite)
     apply (simp add: cprod_cong1 csum_com ordIso_imp_ordLeq)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Card_order_csum cinfinite_csum natLeq_Cinfinite)
      apply (simp add: lam_pre.bd_Cnotzero)
     apply (simp add: natLeq_Cinfinite ordLeq_csum2)
    apply (simp add: csum_absorb1 infinite_regular_card_order.Card_order infinite_regular_card_order.cinfinite infinite_regular_card_order_card_suc natLeq_Cinfinite natLeq_card_order natLeq_ordLeq_cinfinite)
  using Card_order_cprod card_order_on_well_order_on apply blast
  apply (simp add: inj_on_def Abs_ilam_pre_bdT_inject)
  done

lemma supp_bij_cinfset[simp]:
  "|supp (bij_cinfset A B :: 'a \<Rightarrow> 'a)| <o |UNIV :: 'a :: var_ilam_pre set|"
  unfolding bij_cinfset_def supp_def
  apply (rule ordLeq_ordLess_trans[of _ "|set_cinfset A \<union> set_cinfset B|", OF card_of_mono1])
   apply (auto simp: set_cinfset_bound ilam.Un_bound)
  done

abbreviation "eq_on_super g g' X \<equiv> \<forall>x \<in> X. apply_super g x = apply_super g' x"
abbreviation "bij_super g z z' \<equiv> bij_cinfset (apply_super g z) (apply_super g z')"

typedef 'a P_lam_ilam = "UNIV :: unit set" by auto
typedef 'a :: var_ilam_pre U_lam_ilam = "{T :: 'a super \<Rightarrow> nat list \<Rightarrow> 'a ilam.
  (\<exists>X. finite X \<and> (\<forall>g g'. eq_on_super g g' X \<longrightarrow> T g = T g')
     \<and> (\<forall>z z' g a. z \<in> X \<and> z' \<notin> X \<longrightarrow>
       ivvsubst (bij_super g z z') (T g a) = T (swap_super g z z') a))}"
  apply (rule exI[of _ "\<lambda>g a. iVar (get_cinfset (apply_super g undefined) (list_encode a))"] exI[of _ "{undefined}"] CollectI allI)+
  apply (auto 0 4 simp: infinite bij_cinfset_def get_cinfset_inverse idx_cinfset_inverse get_cinfset_in
    dest: apply_super_disjoint[OF get_cinfset_in] apply_super_disjoint[OF _ get_cinfset_in])
  done


setup_lifting type_definition_U_lam_ilam
(*
typedef 'a :: var_ilam_pre U_lam_ilam = "{T :: 'a super \<Rightarrow> nat list \<Rightarrow> 'a ilam.
  \<forall>z z' g a. T (swap_super g z z') a = ivvsubst (bij_cinfset (apply_super g z) (apply_super g z')) (T g a)}"
  apply (rule exI[of _ "\<lambda>g a. iVar (get_cinfset (apply_super g undefined) (list_encode a))"] CollectI allI)+
  apply (auto simp: bij_cinfset_def get_cinfset_in get_cinfset_inverse)
  subgoal for z Z g a
    apply (cases "g undefined = g z")
     apply (auto simp: bij_cinfset_def get_cinfset_in get_cinfset_inverse)
     defer
  apply (simp add: bij_cinfset_def get_cinfset_in get_cinfset_inverse)
  find_theorems ivvsubst iVar
*)
type_synonym 'a PU_lam_ilam = "'a P_lam_ilam \<Rightarrow> 'a U_lam_ilam"

declare lam_pre.rel_eq[relator_eq]
declare lam_pre.rel_mono[relator_mono]
declare lam_pre.rel_compp[symmetric, relator_distr]
declare lam_pre.rel_transfer[transfer_rule]

lemma lam_pre_quot_map[quot_map]: "Quotient R1 Abs1 Rep1 T1 \<Longrightarrow> Quotient R2 Abs2 Rep2 T2 \<Longrightarrow>
  Quotient (rel_lam_pre R1 R2)
    (map_lam_pre (id :: 'a :: var_lam_pre \<Rightarrow> 'a) (id :: 'b :: var_lam_pre \<Rightarrow> 'b) Abs1 Abs2)
    (map_lam_pre id id Rep1 Rep2)
    (rel_lam_pre T1 T2)"
  unfolding Quotient_alt_def5 lam_pre.rel_Grp[of UNIV _ UNIV, simplified, symmetric]
    lam_pre.rel_conversep[symmetric] lam_pre.rel_compp[symmetric]
  by (auto elim: lam_pre.rel_mono_strong)

lemma lam_pre_rel_eq_onp [relator_eq_onp]:
  "(rel_lam_pre (eq_onp P1) (eq_onp P2) :: ('a :: var_lam_pre, 'b :: var_lam_pre, 'c, 'd) lam_pre \<Rightarrow> _ \<Rightarrow> bool) =
   eq_onp (\<lambda>A. Ball (set3_lam_pre A) P1 \<and> Ball (set4_lam_pre A) P2)"
  unfolding fun_eq_iff eq_onp_def
  apply (auto simp: lam_pre.in_rel[OF supp_id_bound bij_id supp_id_bound, simplified lam_pre.map_id]
    lam_pre.set_map supp_id_bound)
     apply blast+
   apply (smt (verit, best) Product_Type.Collect_case_prodD lam_pre.map_cong_id subsetD)
  subgoal for z
  apply (rule exI[of _ "map_lam_pre id id (\<lambda>x. (x, x)) (\<lambda>x. (x, x)) z"])
  apply (auto simp: lam_pre.map_comp[OF supp_id_bound bij_id supp_id_bound] o_def id_def[symmetric]
    lam_pre.set_map supp_id_bound lam_pre.map_id)
    done
  done

lemma iAbs_inject: "(iAbs x e = iAbs x' e') = (\<exists>f :: 'a \<Rightarrow> 'a. bij f \<and> |supp f| <o |UNIV::'a :: var_ilam_pre set|
  \<and> id_on (ifv (iAbs x e)) f \<and> image_cinfset f x = x' \<and> ivvsubst f e = e')"
  unfolding ilam.set
  unfolding iAbs_def ilam.TT_injects0 map_ilam_pre_def comp_def Abs_ilam_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_ilam_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_ilam_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_ilam_pre_def
    Un_empty_right UN_single
  apply (auto simp: ilam_vvsubst_rrename)
  done

lemma image_cinfset_bij_cinfset:
  includes cinfset.lifting
  shows "image_cinfset (bij_cinfset A B) A = B"
  unfolding bij_cinfset_def
  apply transfer
  apply (auto simp add: from_nat_into infinite_imp_nonempty image_iff inj_on_def)
  by (metis from_nat_into_surj to_nat_on_surj)

lemma iAbs_super_eqI: "|X :: 'a set| <o |UNIV :: 'a :: var_ilam_pre set| \<Longrightarrow>
  \<forall>g g'. (\<forall>x\<in>X. apply_super g x = apply_super g' x) \<longrightarrow> (\<forall>a. T g a = T g' a) \<Longrightarrow>
  (\<forall>z z' g a. z \<in> X \<and> z' \<notin> X \<longrightarrow>
       ivvsubst (bij_cinfset (apply_super g z) (apply_super g z')) (T g a) = T (swap_super g z z') a) \<Longrightarrow>
  \<forall>y. y \<noteq> z \<longrightarrow> apply_super g y = apply_super g' y \<Longrightarrow>
  iAbs (apply_super g z) (T g a) = iAbs (apply_super g' z) (T g' a)"
  apply (rule exists_fresh[THEN exE, of "insert z X \<union> set_cinfset (apply_super g z)"])
  apply (meson finite_insert finite_ordLess_infinite2 infinite infinite_card_of_insert ordIso_ordLess_trans set_cinfset_bound var_lam_pre_class.Un_bound)
  subgoal for zz
    apply (rule box_equals[of
      "iAbs (apply_super (swap_super g z zz) z) (T (swap_super g z zz) a)"
      "iAbs (apply_super (swap_super g' z zz) z) (T (swap_super g' z zz) a)"])
      apply simp
      apply (rule arg_cong[of _ _ "iAbs _"])
      apply (drule spec2)
      apply (drule mp)
       prefer 2
       apply (erule spec)
      apply auto []
       apply (simp_all (no_asm))
     apply (rule sym)
     apply (cases "apply_super g z = apply_super g zz")
    apply (smt (verit, ccfv_SIG) apply_super_swap_super)
    subgoal premises prems
      using prems(6)
      unfolding iAbs_inject
      apply (intro exI[of _ "bij_cinfset (apply_super g z) (apply_super g zz)"])
      apply (intro conjI)
          apply (rule bij_cinfset)
          apply transfer
          apply force
         apply (simp_all add: image_cinfset_bij_cinfset ilam_vvsubst_rrename[symmetric])
       prefer 2
      sorry
    sorry
  done

lift_definition CCTOR_lam_ilam :: "('a::var_ilam_pre, 'a, 'a lam \<times> 'a PU_lam_ilam, 'a lam \<times> 'a PU_lam_ilam) lam_pre \<Rightarrow> 'a PU_lam_ilam" is
  "\<lambda>lp :: ('a::var_ilam_pre, 'a, 'a lam \<times> _, 'a lam \<times> _) lam_pre.
     (\<lambda>u :: 'a P_lam_ilam. case Rep_lam_pre lp of
     Inl x \<Rightarrow> \<lambda>g a. iVar (get_cinfset (apply_super g x) (list_encode a))
   | Inr (Inl (M, N)) \<Rightarrow> \<lambda>g a. iApp (snd M u g (0 # a)) (image_cinfmset (\<lambda>i. snd N u g ((i + 1) # a)) \<nat>#)
   | Inr (Inr (x, M)) \<Rightarrow> \<lambda>g a. iAbs (apply_super g x) (snd M u g a))"
  apply (tactic \<open>BNF_Tactics.unfold_thms_tac @{context} [Thm.axiom @{theory} "Mazza.lam_pre.rel_lam_pre_def"] \<close>)
  apply (tactic \<open>BNF_Tactics.unfold_thms_tac @{context} [Thm.axiom @{theory} "Mazza.lam_presum.sum2.sum.Sum_Type.rel_lam_presum_def"] \<close>)
  apply (auto 0 0 simp only: fun_eq_iff vimage2p_def rel_sum.simps rel_fun_def split: sum.splits)
  subgoal for lp1 lp2 x
    apply (rule exI[of _ "{x}"])
    apply auto
    apply (metis (no_types, opaque_lifting) ilam.card_of_FFVars_bounds ilam.set(1) singletonI)
  subgoal for lp1 lp2 M TM2 N TN2 TM1 TN1 u TM3 TN3
    apply (drule spec[of _ u])
    apply (drule spec[of _ u])
    apply safe
    subgoal for XM XN
      apply (rule exI[of _ "XM \<union> XN"])
      apply safe
      using var_lam_pre_class.Un_bound apply blast
      apply (auto intro!: arg_cong2[of _ _ _ _ iApp] arg_cong2[of _ _ _ _ image_cinfmset])
      done
    done
  subgoal for lp1 lp2 x M TM2 TM1 u TM3
    apply (rotate_tac 2)
    apply (drule spec[of _ u])
    apply safe
    subgoal for X
      apply (rule exI[of _ "X - {x}"])
      apply safe
      using card_of_minus_bound apply blast
      apply (rule exists_fresh[THEN exE])
       apply assumption
      subgoal for g g' a z
        find_theorems "iAbs _ _ = iAbs _ _"
      find_theorems "_ <o _ \<Longrightarrow> \<exists> _. _ \<notin> _"

  thm ilam.card_of_FFVars_bounds
  thm sum2.sum.rel_lam_presum
ML \<open>Defs.specifications_of (Theory.defs_of @{theory}) (Defs.Const, @{const_name "sum2.sum.rel_lam_presum"})\<close>
  find_theorems sum2.sum.rel_lam_presum


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
