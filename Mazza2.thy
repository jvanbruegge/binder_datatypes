theory Mazza2
  imports
    "thys/MRBNF_Recursor"
    "HOL-Library.Stream"
    Countably_Infinite_Set
    Countably_Infinite_Multiset
    "thys/Instantiation_Infrastructure/Swapping_vs_Permutation"
    "thys/Instantiation_Infrastructure/FixedUncountableVars"
begin


(* More on streams: *)

definition sdistinct where 
"sdistinct xs \<equiv> \<forall>i j. i \<noteq> j \<longrightarrow> snth xs i \<noteq> snth xs j"

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
| App "'a ilam" "'a ilam stream"
| Abs "X::'a stream" "t::'a ilam" binds X in t
*)

ML \<open>
val ctors = [
  (("iVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("iApp", NONE), [@{typ 'rec}, @{typ "'rec stream"}]),
  (("iAbs", NONE), [@{typ "'bvar stream"}, @{typ 'brec}])
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

lemma inj_iso_partition: "inj (iso_partition x)"
  using bij_iso_partition unfolding bij_def inj_on_def
  by auto

lemma var_partition_cinf: "X \<in> var_partition \<Longrightarrow> countable X \<and> infinite X"
  unfolding var_partition_def
  by (auto intro!: range_inj_infinite[OF inj_iso_partition])

lemma ex1_var_partition: "\<exists>!X. X \<in> var_partition \<and> x \<in> X"
  using partition_var_partition unfolding partition_on_def disjoint_def by auto

lemma Union_var_partition: "(\<Union>X \<in> var_partition. X) = UNIV"
  using ex1_var_partition by fast

lemma bd_ilam_pre_ordIso: "bd_ilam_pre =o card_suc natLeq"
  apply (rule ordIso_symmetric)  
  apply (tactic \<open>BNF_Tactics.unfold_thms_tac @{context} [Thm.axiom @{theory} "Mazza2.ilam_pre.bd_ilam_pre_def"]\<close>)
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
      (*
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
*) sorry

lemma natLeq_less_UNIV: "natLeq <o |UNIV :: 'a :: var_ilam_pre set|"
  apply (rule ordLess_ordLeq_trans[OF _ ilam.var_large])
  apply (rule ordLess_ordIso_trans[OF card_suc_greater[OF natLeq_card_order]])
  apply (rule ordIso_symmetric[OF bd_ilam_pre_ordIso])
  done

lemma infinite_var_partition: "infinite (var_partition :: 'a :: var_ilam_pre set set)"
  apply (rule notI)
  apply (subgoal_tac "countable (UNIV :: 'a :: var_ilam_pre set)")
  using natLeq_less_UNIV not_ordLeq_ordLess countable_card_le_natLeq apply blast
  apply (auto simp: Union_var_partition[symmetric] countable_finite
    dest: var_partition_cinf intro!: countable_UN[of _ "\<lambda>X. X", simplified])
  done

lemma var_partition_ordIso: "|var_partition :: 'a :: var_ilam_pre set set| =o |UNIV :: 'a set|"
  unfolding ordIso_iff_ordLeq
  apply (rule conjI)
   apply (unfold var_partition_def) []
   apply (rule card_of_image)
  apply (unfold Union_var_partition[symmetric])
  apply (rule card_of_UNION_ordLeq_infinite)
    apply (auto simp: infinite_var_partition)
   apply (drule var_partition_cinf)
  apply (auto simp: countable_card_le_natLeq elim!: ordLeq_transitive)
  using infinite_iff_natLeq_ordLeq infinite_var_partition by blast

(*
lift_definition cinf_partition :: "'a :: var_ilam_pre cinfset set" is "var_partition"
  by (auto dest: var_partition_cinf)

lemma cinf_partition_ordIso:
  "|cinf_partition :: 'a :: var_ilam_pre cinfset set| =o |UNIV :: 'a set|"
  unfolding cinf_partition_def
  apply (rule ordIso_transitive[OF _ var_partition_ordIso])
  apply (rule card_of_ordIso[THEN iffD1])
  apply (auto intro!: exI[of _ set_cinfset] inj_onI simp:
    image_image bij_betw_def Abs_cinfset_inverse var_partition_cinf)
  done

lemma infinite_cinf_partition: "infinite (cinf_partition :: 'a :: var_ilam_pre cinfset set)"
  by transfer (rule infinite_var_partition)

lemma cinf_partition: "cinf_partition_on UNIV cinf_partition"
  by transfer (rule partition_var_partition)

lemma cinf_partition_disjoint:
  "X \<in> cinf_partition \<Longrightarrow> Y \<in> cinf_partition \<Longrightarrow> X \<noteq> Y \<Longrightarrow> set_cinfset X \<inter> set_cinfset Y = {}"
  by transfer (meson disjoint_def partition_on_def partition_var_partition)

definition super0 :: "'a ::var_ilam_pre \<Rightarrow> 'a cinfset" where
  "super0 = (SOME f. bij_betw f UNIV cinf_partition)"

definition super ("\<lbrace>_\<rbrace>" [999] 1000) where "super = super0 o embed"

lemma bij_betw_super0: "bij_betw super0 (UNIV :: 'a :: var_ilam_pre set) cinf_partition"
  unfolding super0_def
  apply (rule someI_ex[of "\<lambda>f. bij_betw f UNIV cinf_partition"])
  apply (rule card_of_ordIso[where 'a='a, THEN iffD2, OF ordIso_symmetric[OF var_partition_ordIso], THEN exE])
  unfolding cinf_partition_def
  subgoal for f
    apply (rule exI[of _ "Abs_cinfset o f"])
    apply (rule bij_betw_comp_iff2[THEN iffD1, rotated 2])
    apply assumption
     apply (rule inj_on_imp_bij_betw)
     apply (auto simp: inj_on_def Abs_cinfset_inject dest!: var_partition_cinf elim: bij_betw_apply)
    done
  done

lemma super_inject: "\<lbrace>x\<rbrace> = \<lbrace>y\<rbrace> \<Longrightarrow> x = y"
  unfolding super_def o_apply
  by (meson bij_betw_imp_inj_on bij_betw_super0 injD inj_embed)

lemma disjoint_super: "x \<noteq> y \<Longrightarrow> set_cinfset \<lbrace>x\<rbrace> \<inter> set_cinfset \<lbrace>y\<rbrace> = {}"
  unfolding super_def o_apply
  by (meson UNIV_I bij_betw_apply bij_betw_imp_inj_on bij_betw_super0 cinf_partition_disjoint injD inj_embed)
*)

lemma bij_betw_swap: "bij_betw f A B \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow>  bij_betw (f(a := f b, b := f a)) A B"
  apply (auto simp: bij_betw_def image_iff)
  apply (auto simp: inj_on_def)
  done

instantiation ivar :: var_ilam_pre begin
instance
  apply standard
    apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF card_ivar]])
    apply (rule ordIso_ordLeq_trans[OF card_of_Field_natLeq])
    apply (rule ordLess_imp_ordLeq)
    apply (rule cardSuc_greater[OF natLeq_Card_order])
   apply (rule regularCard_ordIso[OF ordIso_symmetric[OF card_ivar]])
    apply (simp add: Cinfinite_cardSuc natLeq_Card_order natLeq_cinfinite)
   apply (simp add: natLeq_Cinfinite regularCard_cardSuc)
  apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF card_ivar]])

  (* apply (metis Field_card_suc cardSuc_ordIso_card_suc card_order_card_suc Un_iff card_of_unique
    natLeq_card_order ordIso_symmetric ordIso_transitive ordLeq_ordLess_Un_ordIso) 
  done *)
  sorry
end

subclass (in cinf) var_lam_pre
  apply standard
  using Field_natLeq infinite_iff_card_of_nat infinite apply auto[1]
  apply (rule regularCard_ordIso[OF _ natLeq_Cinfinite regularCard_natLeq])
  apply (meson card_of_nat countable_def countable_or_card_of ex_inj local.infinite ordIso_symmetric ordIso_transitive)
  done

(*
lemma small_super:
  fixes g :: "'a :: cinf \<Rightarrow> ivar cinfset"
  shows "infinite A \<Longrightarrow> inj g \<Longrightarrow> cinf_partition_on UNIV X \<Longrightarrow> g ` A \<subseteq> X \<Longrightarrow> infinite (X - g ` A)"
  apply (rule subset_ordLeq_diff_infinite)
    apply (rule countable_as_injective_image[of "g ` A"])
      apply (rule countable_image)
      apply blast
     apply (simp add: finite_image_iff inj_on_subset[OF _ subset_UNIV])
    apply (metis cinf_class.infinite inj_on_finite)
   apply (metis)
  apply (rule ccontr)
  apply simp
  apply (subst (asm) card_of_ordLeq2[symmetric])
   apply (auto simp: image_iff)
  apply transfer
  apply (auto simp: subset_eq image_iff partition_on_def disjoint_def)
  apply (metis UNIV_I countableI_type countable_UN exists_ivar)
  done

definition "pw_disjoint ZZ = (\<forall>X \<in> ZZ. \<forall>Y \<in> ZZ. X \<noteq> Y \<longrightarrow> set_cinfset X \<inter> set_cinfset Y = {})"

definition "is_super g = (inj g \<and> pw_disjoint (range g))"

typedef 'a :: cinf super = "{g :: 'a \<Rightarrow> ivar cinfset. is_super g}"
   morphisms apply_super Rep_super
  using bij_betw_super0 unfolding is_super_def pw_disjoint_def
  apply (auto intro!: exI[of _ super] inj_compose
    simp: super_def bij_betw_def inj_embed cinf_partition)
  by (metis Int_emptyD cinf_partition_disjoint range_eqI)

setup_lifting type_definition_super

lift_definition comp_super :: "'a :: cinf super \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a :: cinf super" is
  "\<lambda>g f. if inj f then g o f else g"
  unfolding is_super_def pw_disjoint_def
  by (auto intro!: inj_compose dest: Int_emptyD injD)
*)
lemma range_swap: "range (g(z := g z', z' := g z)) = range g"
  by auto

(*
lemma is_super_swap: "is_super g \<Longrightarrow> is_super (g(y := g x, x := g y))"
  unfolding is_super_def pw_disjoint_def
  by (fastforce simp: inj_on_def split: if_splits)

lift_definition swap_super :: "'a :: cinf super \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a :: cinf super" is
  "\<lambda>g z z'. g (z := g z', z' := g z)"
  by (rule is_super_swap)

lemma swap_super_self[simp]: "swap_super g x x = g"
  by transfer auto

lemma apply_super_eqI:
  "x \<in>\<in> apply_super g z \<Longrightarrow> x \<in>\<in> apply_super g z' \<Longrightarrow> apply_super g z = apply_super g z'"
  by transfer (auto simp: is_super_def pw_disjoint_def)

lemma apply_super_swap_super[simp]: "apply_super (swap_super g z z') x =
  (if x = z then apply_super g z' else if x = z' then apply_super g z else apply_super g x)"
  by transfer auto

definition bij_cinfset where
  "bij_cinfset A B x = (if x \<in>\<in> A then get_cinfset B (idx_cinfset A x)
     else if x \<in>\<in> B then get_cinfset A (idx_cinfset B x)
     else x)"

lemma bij_cinfset_self[simp]: "bij_cinfset X X = id"
  unfolding bij_cinfset_def
  by transfer auto

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

*)

lemma card_of_set_cinfset: "|set_cinfset A| =o natLeq"
  using bij_betw_idx_cinfset card_of_nat card_of_ordIso ordIso_transitive by blast

subclass (in var_ilam_pre) var_lam_pre
  by standard

(*
lemma set_cinfset_bound: "|set_cinfset A :: 'a set| <o |UNIV :: 'a :: var_ilam_pre set|"
  by (rule ordIso_ordLess_trans[OF card_of_set_cinfset natLeq_less_UNIV])

lemma supp_bij_cinfset[simp]:
  "|supp (bij_cinfset A B :: 'a \<Rightarrow> 'a)| <o |UNIV :: 'a :: var_ilam_pre set|"
  unfolding bij_cinfset_def supp_def
  by (rule ordLeq_ordLess_trans[of _ "|set_cinfset A \<union> set_cinfset B|", OF card_of_mono1])
    (auto simp: set_cinfset_bound ilam.Un_bound)

lemma inj_apply_super: "inj (apply_super g)"
  by transfer (auto simp: is_super_def)

lemma apply_super_disjoint: "z \<noteq> z' \<Longrightarrow> set_cinfset (apply_super g z) \<inter> set_cinfset (apply_super g z') = {}"
  by transfer (fastforce simp: is_super_def inj_on_def pw_disjoint_def)

abbreviation "eq_on_super g g' X \<equiv> \<forall>x \<in> X. apply_super g x = apply_super g' x"
abbreviation "bij_super g z z' \<equiv> bij_cinfset (apply_super g z) (apply_super g z')"

typedef 'a P_lam_ilam = "UNIV :: unit set" by auto
typedef 'a :: cinf U_lam_ilam = "{T :: 'a super \<Rightarrow> nat list \<Rightarrow> ivar ilam.
  (\<exists>X. finite X \<and> (\<forall>g g'. eq_on_super g g' X \<longrightarrow> T g = T g')
     \<and> (\<forall>z z' g a. z' \<notin> X \<longrightarrow>  ivvsubst (bij_super g z z') (T g a) = T (swap_super g z z') a)
     \<and> (\<forall>g a. ifv (T g a) \<subseteq> (\<Union>z \<in> X. set_cinfset (apply_super g z))))}"
  apply (rule exI[of _ "\<lambda>g a. iVar (get_cinfset (apply_super g undefined) (list_encode a))"] exI[of _ "{undefined}"] CollectI allI)+
  apply (auto 0 4 simp: infinite bij_cinfset_def get_cinfset_inverse idx_cinfset_inverse get_cinfset_in
    dest: apply_super_eqI[OF get_cinfset_in] apply_super_eqI[OF _ get_cinfset_in])
  apply (meson Int_emptyD apply_super_disjoint get_cinfset_in)
  apply (meson Int_emptyD apply_super_disjoint get_cinfset_in)
  done

setup_lifting type_definition_U_lam_ilam

type_synonym 'a PU_lam_ilam = "'a P_lam_ilam \<Rightarrow> 'a U_lam_ilam"
*)

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

lemmas stream.set_map[simp] lemmas stream.map_id[simp]

lemma iAbs_inject: "(iAbs x e = iAbs x' e') = (\<exists>f :: 'a \<Rightarrow> 'a. bij f \<and> |supp f| <o |UNIV::'a :: var_ilam_pre set|
  \<and> id_on (ifv (iAbs x e)) f \<and> smap f x = x' \<and> ivvsubst f e = e')"
  unfolding ilam.set
  unfolding iAbs_def ilam.TT_injects0 map_ilam_pre_def comp_def Abs_ilam_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_ilam_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_ilam_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_ilam_pre_def
    Un_empty_right UN_single
  apply (auto simp: ilam_vvsubst_rrename)   
  done

lemma iVar_inject[simp]: "(iVar x = iVar x') = (x = x')"
  unfolding ilam.set
  unfolding iVar_def ilam.TT_injects0 map_ilam_pre_def comp_def Abs_ilam_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_ilam_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_ilam_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_ilam_pre_def
    Un_empty_right UN_single
  apply (auto simp: ilam_vvsubst_rrename id_def[symmetric] cinfmset.map_id supp_id_bound intro!: exI[of _ id])
  done

lemma iApp_inject[simp]: "(iApp t U = iApp t' U') = (t = t' \<and> U = U')"
  unfolding ilam.set
  unfolding iApp_def ilam.TT_injects0 map_ilam_pre_def comp_def Abs_ilam_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_ilam_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_ilam_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_ilam_pre_def
    Un_empty_right UN_single
  apply (auto simp: ilam_vvsubst_rrename id_def[symmetric] cinfmset.map_id supp_id_bound intro!: exI[of _ id])
  done

(*
lemma image_cinfset_bij_cinfset[simp]:
  includes cinfset.lifting
  shows "image_cinfset (bij_cinfset A B) A = B"
  unfolding bij_cinfset_def
  apply transfer
  apply (auto simp add: from_nat_into infinite_imp_nonempty image_iff inj_on_def)
  by (metis from_nat_into_surj to_nat_on_surj)

lemma image_cinfset_bij_cinfset':
  includes cinfset.lifting
  assumes "set_cinfset A \<inter> set_cinfset B = {}"
  shows "image_cinfset (bij_cinfset A B) B = A"
  unfolding bij_cinfset_def using assms
  apply transfer
  apply (auto simp add: from_nat_into infinite_imp_nonempty image_iff inj_on_def)
  by (metis Int_Collect Int_iff emptyE from_nat_into_surj to_nat_on_surj)

lemma bij_bij_super[simp]: "bij (bij_super g z z')"
  by (metis apply_super_disjoint bij_cinfset bij_cinfset_self bij_id)

lemma image_cinfset_bij_super_idle[simp]: "x \<noteq> z \<Longrightarrow> x \<noteq> z' \<Longrightarrow> image_cinfset (bij_super g z z') (apply_super g x) = apply_super g x"
  apply (rule trans[OF cinfset.map_cong cinfset.map_id])
       apply (auto simp: supp_id_bound)
  apply (auto simp: bij_cinfset_def dest: apply_super_disjoint)
  done

lemma image_cinfset_bij_super'[simp]:
  "image_cinfset (bij_super g z z') (apply_super g z') = apply_super g z"
  apply (cases "z = z'")
  apply (simp add: cinfset.map_id)
  apply (erule image_cinfset_bij_cinfset'[OF apply_super_disjoint])
  done
*)

lemma cinf_small_iff_finite[simp]: "|A :: 'b set| <o |UNIV :: 'a :: cinf set| \<longleftrightarrow> finite A"
  apply (auto simp: finite_iff_cardOf_nat elim!: ordLess_ordLeq_trans[rotated])
   apply (meson countableI_type countable_card_of_nat ordLess_ordLeq_trans)
  apply (meson UNIV_I exists_fresh finite_iff_ordLess_natLeq infinite_iff_card_of_nat
    var_lam_pre_class.large ordLess_ordLeq_trans)
  done

(*
lemma iAbs_super_eqI0: "finite X \<Longrightarrow>
  \<forall>g g'. (\<forall>x\<in>X. apply_super g x = apply_super g' x) \<longrightarrow> (\<forall>a. T g a = T g' a) \<Longrightarrow>
  (\<forall>z z' g a. z' \<notin> X \<longrightarrow>
    ivvsubst (bij_cinfset (apply_super g z) (apply_super g z')) (T g a) = T (swap_super g z z') a) \<Longrightarrow>
  (\<forall>g a. ifv (T g a) \<subseteq> (\<Union>z \<in> insert z X. set_cinfset (apply_super g z))) \<Longrightarrow>
  \<forall>y. y \<noteq> z \<longrightarrow> apply_super g y = apply_super g' y \<Longrightarrow>
  iAbs (apply_super g z) (T g a) = iAbs (apply_super g' z) (T g' a)"
  apply (rule exists_fresh[THEN exE, of "insert z X"])
    apply simp_all
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
     apply (rule sym)
    subgoal premises prems
      using prems(3,6) prems(4)[rule_format, of g a]
      unfolding iAbs_inject
      apply (intro exI[of _ "bij_super g z zz"])
      apply (auto simp: id_on_def bij_cinfset_def subset_eq)
      apply (metis Int_emptyD apply_super_disjoint)
      done
     apply (rule sym)
    subgoal premises prems
      using prems(3,6) prems(4)[rule_format, of g' a]
      unfolding iAbs_inject
      apply (intro exI[of _ "bij_super g' z zz"])
      apply (auto simp: id_on_def bij_cinfset_def subset_eq)
      apply (metis Int_emptyD apply_super_disjoint)
      done
    done
  done

lemma iAbs_super_eqI: "\<forall>y. y \<noteq> z \<longrightarrow> apply_super g y = apply_super g' y \<Longrightarrow>
  iAbs (apply_super g z) (Rep_U_lam_ilam T g a) = iAbs (apply_super g' z) (Rep_U_lam_ilam T g' a)"
  using Rep_U_lam_ilam[of T]
  by (fastforce elim!: iAbs_super_eqI0)
*)

lemma ivvsubst_bij_iAbs:
  fixes f :: "'a :: var_ilam_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV :: 'a set|"
  shows "ivvsubst f (iAbs x t) = iAbs (smap f x) (ivvsubst f t)"
  unfolding iAbs_def ilam_vvsubst_rrename[OF assms] ilam.rrename_cctors[OF assms]
  by (auto simp: map_ilam_pre_def Abs_ilam_pre_inverse)

context includes cinfmset.lifting begin

lemma in_image_cinfmset: "y \<in>#\<in> image_cinfmset f X \<longleftrightarrow> y \<in> f ` set_cinfmset X"
  apply transfer
  apply (auto simp: Let_def image_iff)
   apply (metis (mono_tags, lifting) disjoint_iff_not_equal finite.emptyI mem_Collect_eq vimage_singleton_eq)+
  done

lemma NATS_cinfmset_UNIV: "i \<in>#\<in> \<nat>#"
  by transfer auto

end

(*
lift_definition CCTOR_lam_ilam :: "('a::cinf, 'a, 'a lam \<times> 'a PU_lam_ilam, 'a lam \<times> 'a PU_lam_ilam) lam_pre \<Rightarrow> 'a PU_lam_ilam" is
  "\<lambda>lp :: ('a::cinf, 'a, 'a lam \<times> _, 'a lam \<times> _) lam_pre.
     (\<lambda>u :: 'a P_lam_ilam. case Rep_lam_pre lp of
     Inl x \<Rightarrow> \<lambda>g a. iVar (get_cinfset (apply_super g x) (list_encode a))
   | Inr (Inl (M, N)) \<Rightarrow> \<lambda>g a. iApp (snd M u g (0 # a)) (image_cinfmset (\<lambda>i. snd N u g ((i + 1) # a)) \<nat>#)
   | Inr (Inr (x, M)) \<Rightarrow> \<lambda>g a. iAbs (apply_super g x) (snd M u g a))"
  apply (tactic \<open>BNF_Tactics.unfold_thms_tac @{context} [Thm.axiom @{theory} "Mazza.lam_pre.rel_lam_pre_def"] \<close>)
  apply (tactic \<open>BNF_Tactics.unfold_thms_tac @{context} [Thm.axiom @{theory} "Mazza.lam_presum.sum2.sum.Sum_Type.rel_lam_presum_def"] \<close>)
  apply (auto 0 0 simp only: fun_eq_iff vimage2p_def rel_sum.simps rel_fun_def rel_prod.simps split: sum.splits)
  subgoal for lp1 lp2 x
    apply (rule exI[of _ "{x}"])
    apply (auto simp add: bij_cinfset_def get_cinfset_in get_cinfset_inverse)
    apply (metis Int_emptyD apply_super_disjoint idx_cinfset_inverse)
    apply (meson Int_emptyD apply_super_disjoint get_cinfset_in)
    apply (meson Int_emptyD apply_super_disjoint get_cinfset_in)
    done
  subgoal for lp1 lp2 M N TM2 TN2 TM1 TN1 u
    apply (drule spec[of _ u])+
    apply (drule mp, rule refl)+
    apply safe
    subgoal for XM XN
      apply (rule exI[of _ "XM \<union> XN"])
      apply (auto simp: cinfmset_map_comp subset_eq in_image_cinfmset intro!: arg_cong2[of _ _ _ _ image_cinfmset])
      apply meson
      done
    done
  subgoal for lp1 lp2 M N TM2 TN2 TM1 TN1 u g a
    apply (drule spec[of _ u])+
    apply (drule mp, rule refl)+
    apply fastforce
    done
  subgoal for lp1 lp2 x M TM1 TM2 u
    apply (drule spec[of _ u])+
    apply (drule mp, rule refl)+
    apply safe
    subgoal for X
      apply (rule exI[of _ "insert x X"])
      apply (clarsimp simp add: ilam.map_id ivvsubst_bij_iAbs cinfset.map_id)
      apply fastforce
      done
    done
  subgoal for lp1 lp2 x M TM1 TM2 u g a
    apply (drule spec[of _ u])+
    apply (drule mp, rule refl)+
    apply auto
    done
  done

lemma apply_super_comp_super[simp]: "inj f \<Longrightarrow> apply_super (comp_super g f) = apply_super g o f"
  apply transfer
  apply auto
  done

lemma apply_super_comp_super'[simp]: "bij f \<Longrightarrow> apply_super (comp_super g f) = apply_super g o f"
  by (rule apply_super_comp_super[OF bij_is_inj])

lemma comp_super_swap_super[simp]: "bij f \<Longrightarrow>
  comp_super (swap_super g z z') f =
  swap_super (comp_super g f) (inv f z) (inv f z')"
  by transfer (auto simp: fun_eq_iff inv_f_eq dest: bij_is_inj)

lift_definition map_U_lam_ilam :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a lam \<Rightarrow> 'a U_lam_ilam \<Rightarrow> 'a :: cinf U_lam_ilam" is
  "\<lambda>f t T g a. if bij f then T (comp_super g f) a else T g a"
  apply safe
  subgoal for f _ T X
    apply (intro exI[of _ "if bij f then f ` X else X"] conjI)
       apply (clarsimp simp add: fun_eq_iff)+
    subgoal for z z' g a
      apply (drule spec[of _ "inv f z"])
      apply (drule spec[of _ "inv f z'"])
      apply (drule mp)
       apply force
      apply (rotate_tac -1)
      apply (drule spec2[of _ "comp_super g f" a])
      apply auto
      done
    apply clarsimp
    subgoal for g a z
      apply (drule spec2[of _ "comp_super g f" a])
      apply auto
      done
    done
  done

lift_definition set_U_lam_ilam :: " 'a lam \<Rightarrow> 'a :: cinf U_lam_ilam \<Rightarrow> 'a set" is
  "\<lambda>t T. {x. \<exists>g g' a. (T g a \<noteq> T g' a \<and> (\<forall>y. y \<noteq> x \<longrightarrow> apply_super g y = apply_super g' y))}"
  .

lemma map_sum_eq_conv:
  "map_sum f g x = Inl y \<longleftrightarrow> (\<exists>l. x = Inl l \<and> y = f l)"
  "map_sum f g x = Inr z \<longleftrightarrow> (\<exists>r. x = Inr r \<and> z = g r)"
  "Inl y = map_sum f g x \<longleftrightarrow> (\<exists>l. x = Inl l \<and> y = f l)"
  "Inr z = map_sum f g x \<longleftrightarrow> (\<exists>r. x = Inr r \<and> z = g r)"
  by (cases x; auto)+

lemma comp_super_id[simp]: "comp_super g id = g"
  by transfer auto

lemma map_U_lam_ilam_id: "map_U_lam_ilam id t = id"
  by transfer' auto

lemma comp_super_comp[simp]: "inj f \<Longrightarrow> inj h \<Longrightarrow> comp_super (comp_super g f) h = comp_super g (f o h)"
  by transfer (auto simp: inj_compose)

lemma comp_super_cong_id: "(\<forall>x. f x = x) \<Longrightarrow> comp_super g f = g"
  by transfer auto

lemma map_U_lam_ilam_comp:
  fixes f g :: "'a :: cinf \<Rightarrow> 'a"
  shows "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a :: cinf set| \<Longrightarrow> bij g \<Longrightarrow> |supp g| <o |UNIV :: 'a :: cinf set| \<Longrightarrow>
   map_U_lam_ilam (f \<circ> g) t = map_U_lam_ilam f t \<circ> map_U_lam_ilam g t"
  by transfer' (auto simp: fun_eq_iff dest!: bij_is_inj)

lemma comp_super_swap[simp]: "comp_super g (id(x := y, y := x)) = swap_super g x y"
  by transfer (auto simp: bij_swap[THEN bij_is_inj])

lemma exists_fresh_super:
  fixes g :: "'a :: cinf \<Rightarrow> ivar cinfset"
  shows "inj g \<Longrightarrow> pw_disjoint (range g) \<Longrightarrow>
  \<exists>Z. Z \<notin> range g \<and> pw_disjoint (insert Z (range g))"
  unfolding pw_disjoint_def
  apply transfer
  apply clarsimp
  subgoal premises prems for g
  proof -
    have "|\<Union>x \<in> UNIV. g x| <o |UNIV :: ivar set|"
      apply (rule ilam.UNION_bound)
       apply (rule ordIso_ordLess_trans[OF _ natLeq_less_UNIV])
       apply (meson card_of_card_order_on card_of_ordLeqI card_order_on_ordIso
          cinf_class.infinite ex_inj exists_univ_eq finite_iff_cardOf_nat natLeq_card_order
          ordLeq_iff_ordLess_or_ordIso ordLeq_ordIso_trans ordLess_ordIso_trans)
      using countable_card_ivar prems(1) apply blast
      done
    then have "infinite (UNIV - (\<Union>x \<in> UNIV. g x))"
      by (rule subset_ordLeq_diff_infinite[rotated 2]) (auto simp: infinite_ivar)
    with infinite_countable_subset'[OF this] obtain Z where
      "Z \<inter> \<Union>(range g) = {}" "countable Z" "infinite Z"
      by auto
    then show ?thesis
      apply (intro exI[of _ Z])
      apply auto
      by (metis Union_disjoint finite.emptyI inf.idem inf_commute rangeI)
  qed
  done

lift_definition refresh :: "'a :: cinf super \<Rightarrow> 'a \<Rightarrow> 'a :: cinf super" is
  "\<lambda>g x. g(x := SOME Y. Y \<notin> range g \<and> pw_disjoint (insert Y (range g)))"
  subgoal for g a
    unfolding is_super_def
    apply (rule someI2_ex[where P="\<lambda>Y. Y \<notin> range g \<and> pw_disjoint (insert Y (range g))"])
    apply (rule exists_fresh_super)
    apply (auto simp: inj_on_def pw_disjoint_def)
    done
  done

lifting_update cinfset.lifting
lifting_forget cinfset.lifting

lift_definition plug :: "'a \<Rightarrow> ivar cinfset \<Rightarrow> 'a super \<Rightarrow> 'a :: cinf super" is
  "\<lambda>x Y g. let h = g(x := Y) in if is_super h then h else g"
  by (auto simp: Let_def is_super_def)

lemma apply_super_refresh: "x \<noteq> y \<Longrightarrow> apply_super (refresh g x) y = apply_super g y"
  by transfer auto

lemma apply_super_plug: "x \<noteq> y \<Longrightarrow> apply_super (plug x Y g) y = apply_super g y"
  by transfer (auto simp: Let_def)

lemma super_eqI: "\<forall>x. apply_super g x = apply_super g' x \<Longrightarrow> g = g'"
  by transfer auto

lemma swap_super_dance:
  "x \<noteq> y \<Longrightarrow> plug x (apply_super g y) (plug y (apply_super g x) (refresh (refresh g x) y)) =
  swap_super g x y"
  apply (rule super_eqI)
  apply (auto simp: apply_super_plug apply_super_refresh)
  subgoal
    apply (transfer fixing: x y)
    apply (unfold Let_def[where 'a = "'a \<Rightarrow> ivar cinfset"])
    apply (subst if_P)
    subgoal for g
      apply (rule someI2_ex[where P="\<lambda>Y. Y \<notin> range g \<and> pw_disjoint (insert Y (range g))"])
       apply (rule exists_fresh_super)
      apply (auto simp: is_super_def pw_disjoint_def inj_on_def)
      done
    apply simp
    done
  subgoal
    apply (transfer fixing: x y)
    apply (unfold Let_def[where 'a = "'a \<Rightarrow> ivar cinfset"])
    apply (subst if_P)
    subgoal for g
      apply (rule someI2_ex[where P="\<lambda>Y. Y \<notin> range g \<and> pw_disjoint (insert Y (range g))"])
       apply (rule exists_fresh_super)
      apply (auto simp: is_super_def pw_disjoint_def inj_on_def)
      done
    apply (simp add: is_super_swap)
    done
  done

lemma map_U_lam_ilam_cong_swap:
  fixes x y :: "'a :: cinf"
  shows "x \<notin> set_U_lam_ilam t d \<Longrightarrow> y \<notin> set_U_lam_ilam t d \<Longrightarrow> map_U_lam_ilam (id(x := y, y := x)) t d = d"
  apply (cases "x = y")
  apply (simp add: map_U_lam_ilam_id)
  apply (transfer fixing: x y t)
  apply (auto simp: fun_eq_iff)
  subgoal premises prems for T X g a
  proof -
    let ?X = "apply_super g x"
    let ?Y = "apply_super g y"
    have "T g a = T (refresh g x) a"
      using prems(1)[rule_format, of g "refresh g x"]
      by (auto simp: apply_super_refresh)
    also have "\<dots> = T (refresh (refresh g x) y) a"
      using prems(2)[rule_format, of "refresh g x" "refresh (refresh g x) y"]
      by (auto simp: apply_super_refresh)
    also have "\<dots> = T (plug y ?X (refresh (refresh g x) y)) a"
      using prems(2)[rule_format, of "refresh (refresh g x) y" "plug y ?X (refresh (refresh g x) y)"]
      by (auto simp: apply_super_plug)
    also have "\<dots> = T (plug x ?Y (plug y ?X (refresh (refresh g x) y))) a"
      using prems(1)[rule_format, of "plug y ?X (refresh (refresh g x) y)"
        "plug x ?Y (plug y ?X (refresh (refresh g x) y))"]
      by (auto simp: apply_super_plug)
    also have "\<dots> = T (swap_super g x y) a"
      unfolding swap_super_dance[OF \<open>x \<noteq> y\<close>] ..
    finally show ?thesis by (rule sym)
  qed
  done

lemma map_U_lam_ilam_cong_id:
  fixes f :: "'a :: cinf \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV :: 'a :: cinf set|"
    "(\<And>a. a \<in> set_U_lam_ilam t d \<Longrightarrow> f a = a)"
  shows "map_U_lam_ilam f t d = d"
proof -
  from fsupp_ex_compose_even_stronger[of f] assms(1,2)
  obtain \<pi> ::  "('a \<times> 'a) list" where f: "f = compose \<pi>" and nonred: "nonredundant \<pi>"
    by (auto simp: fsupp_def supp_def)
  moreover have "set_U_lam_ilam t d \<inter> supp f = {}" using assms(3)
    by (auto simp: supp_def)
  ultimately show ?thesis
  proof (induct \<pi> arbitrary: f rule: list_induct_Pair)
    case Nil
    then show ?case
      by (simp add: id_def[symmetric] map_U_lam_ilam_id)
  next
    case (Cons x y \<pi>)
    from Cons(3,4) nonredundant_Cons[OF Cons(3)] have "set_U_lam_ilam t d \<inter> supp (compose \<pi>) = {}"
      "x \<notin> set_U_lam_ilam t d" "y \<notin> set_U_lam_ilam t d"
      unfolding Cons(2)
        apply (auto simp del: compose.simps simp: supp_def dest!: nonredundant_compose)
      by (metis (mono_tags, lifting) Int_emptyD mem_Collect_eq)
    then show ?case
      using bij_compose[of \<pi>] supp_swap_bound[of x y, OF infinite] Cons(3)
      unfolding Cons(2) compose.simps
      apply (subst map_U_lam_ilam_comp)
          apply (simp_all add: inj_def bij_is_inj) [4]
       apply (metis fsupp_compose fsupp_def supp_def)
      apply simp
      apply (subst Cons(1)[OF refl])
        apply (simp_all add: nonredundant_Cons map_U_lam_ilam_cong_swap)
      done
  qed
qed

lemma set_U_lam_ilam_map_U_lam_ilam:
  fixes f :: "'a :: cinf \<Rightarrow> 'a"
  shows "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a :: cinf set| \<Longrightarrow>
    set_U_lam_ilam (rrename_lam f t) (map_U_lam_ilam f t d) = f ` set_U_lam_ilam t d"
  apply transfer
  apply (auto simp: image_iff)
  apply (smt (z3) apply_super_comp_super' comp_def bij_implies_inject)
  subgoal for f T X z g g' a
    apply (rule exI[of _ "comp_super g (inv f)"])
    apply (rule exI[of _ "comp_super g' (inv f)"])
    apply (auto dest: spec[of _ "inv f _"] simp: bij_is_inj)
    done
  done

lemma map_CCTOR_lam_ilam:
  "bij f \<Longrightarrow>
       |supp f| <o |UNIV| \<Longrightarrow>
       map_U_lam_ilam f (lam_ctor (map_lam_pre id id fst fst y))
        (CCTOR_lam_ilam y p) =
       CCTOR_lam_ilam
        (map_lam_pre f f
          (\<lambda>(t, pu). (rrename_lam f t, \<lambda>p. map_U_lam_ilam f t (pu (id p))))
          (\<lambda>(t, pu). (rrename_lam f t, \<lambda>p. map_U_lam_ilam f t (pu (id p)))) y)
        (id p)"
  apply (rule iffD1[OF Rep_U_lam_ilam_inject])
  apply (auto simp add: map_U_lam_ilam.rep_eq CCTOR_lam_ilam.rep_eq map_lam_pre_def
    Abs_lam_pre_inverse map_sum_eq_conv
      Var_def[symmetric] App_def[symmetric] Abs_def[symmetric] split: sum.splits)
  done

lemma set_CCTOR_lam_ilam: "set2_lam_pre y \<inter> ({} \<union> {}) = {} \<Longrightarrow>
  set2_lam_pre y \<inter> ({} \<union> {}) = {} \<Longrightarrow>
       (\<And>t pu p. (t, pu) \<in> set3_lam_pre y \<union> set4_lam_pre y \<Longrightarrow> set_U_lam_ilam t (pu p) \<subseteq> fv t \<union> {} \<union> {}) \<Longrightarrow>
       set_U_lam_ilam t (CCTOR_lam_ilam y p) \<subseteq> fv (lam_ctor (map_lam_pre id id fst fst y)) \<union> {} \<union> {}"
  apply clarsimp
  apply (auto simp add: set_U_lam_ilam_def CCTOR_lam_ilam.rep_eq map_lam_pre_def
      set3_lam_pre_def set4_lam_pre_def Abs_lam_pre_inverse map_sum_eq_conv subset_eq
      Var_def[symmetric] App_def[symmetric] Abs_def[symmetric] split: sum.splits)
      apply metis
     apply metis
    apply metis
  subgoal for x z g t g' T a
    apply (erule contrapos_np)
     apply (metis (no_types, lifting) iAbs_super_eqI)
    done
  subgoal for z g t g' T a
    apply (erule contrapos_np)
     apply (metis (no_types, lifting) iAbs_super_eqI)
    done
  done

local_setup \<open>fn lthy =>
let
  fun rtac ctxt = resolve_tac ctxt o single
  val model_tacs = {
    Umap_id0 = fn ctxt => rtac ctxt @{thm map_U_lam_ilam_id} 1,
    Umap_comp0 = fn ctxt => (rtac ctxt @{thm map_U_lam_ilam_comp} THEN_ALL_NEW assume_tac ctxt) 1,
    Umap_cong_id = fn ctxt => (rtac ctxt @{thm map_U_lam_ilam_cong_id}
       THEN_ALL_NEW FIRST' [assume_tac ctxt, Goal.assume_rule_tac ctxt]) 1,
    UFVars_Umaps = [fn ctxt => (rtac ctxt @{thm set_U_lam_ilam_map_U_lam_ilam} THEN_ALL_NEW assume_tac ctxt) 1],
    Umap_Uctor = fn ctxt => (rtac ctxt @{thm map_CCTOR_lam_ilam} THEN_ALL_NEW assume_tac ctxt) 1,
    UFVars_subsets = [fn ctxt => (rtac ctxt @{thm set_CCTOR_lam_ilam}
       THEN_ALL_NEW FIRST' [assume_tac ctxt, Goal.assume_rule_tac ctxt]) 1]
  } : (Proof.context -> tactic) MRBNF_Recursor.model_axioms;

  val params = {
    P = @{typ "('a :: cinf) P_lam_ilam"},
    PFVarss = [@{term "\<lambda>_ :: 'a P_lam_ilam. {} :: 'a :: cinf set"}],
    Pmap = @{term "\<lambda>(_ :: 'a \<Rightarrow> 'a). id :: 'a :: cinf P_lam_ilam \<Rightarrow> 'a P_lam_ilam"},
    avoiding_sets = [ @{term "{} :: 'a::cinf set"}],
    axioms = {
      small_avoiding_sets = [fn ctxt => rtac ctxt @{thm emp_bound} 1],
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
    binding = Binding.name "lam_ilam",
    U = @{typ "'a :: cinf U_lam_ilam"},
    UFVarss = [@{term "set_U_lam_ilam :: 'a lam \<Rightarrow> 'a U_lam_ilam \<Rightarrow> 'a :: cinf set"}],
    Umap = @{term "map_U_lam_ilam :: ('a \<Rightarrow> 'a) \<Rightarrow> 'a lam \<Rightarrow> 'a U_lam_ilam \<Rightarrow> 'a :: cinf U_lam_ilam"},
    Uctor = @{term CCTOR_lam_ilam},
    axioms = model_tacs
  } : (Proof.context -> tactic) MRBNF_Recursor.model;
  val _ = model;
  val (ress, lthy) = MRBNF_Recursor.create_binding_recursor (Binding.qualify false "lam_ilam") fp_res params [model] lthy;
  val res = hd ress;
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

lift_definition super_lifted :: "'a :: cinf super" is super
  unfolding is_super_def pw_disjoint_def super_def
  apply (intro conjI CollectI ballI impI)
  subgoal using bij_betw_super0 by (auto intro!: inj_compose inj_embed simp: bij_betw_def)
  subgoal for X Y
    apply (rule Int_emptyI)
    subgoal for z
      using cinf_partition_on_in_iff[OF cinf_partition, of z, THEN iffD1, OF UNIV_I] bij_betw_super0
      by (metis UNIV_I bij_betw_iff_bijections fun.set_map image_iff)
    done
  done

abbreviation lam_ilam :: "'a :: cinf lam \<Rightarrow> nat list \<Rightarrow> ivar ilam" ("\<lbrakk>_\<rbrakk>_" [999, 1000] 1000) where
   "lam_ilam t a \<equiv> Rep_U_lam_ilam (ff0_lam_ilam t (Abs_P_lam_ilam ())) super_lifted a"

lemma lam_ilam_simps[simp]:
  "\<lbrakk>Var x\<rbrakk>a = iVar (get_cinfset \<lbrace>x\<rbrace> (list_encode a))"
  "\<lbrakk>Abs x M\<rbrakk>a = iAbs \<lbrace>x\<rbrace> (\<lbrakk>M\<rbrakk>a)"
  "\<lbrakk>App M N\<rbrakk>a = iApp \<lbrakk>M\<rbrakk>(0#a) (image_cinfmset (\<lambda>i. \<lbrakk>N\<rbrakk>((i + 1) # a)) \<nat>#)"
  unfolding Var_def Abs_def App_def
    apply (subst lam_ilam.ctor; auto simp: noclash_lam_def set1_lam_pre_def set2_lam_pre_def map_lam_pre_def
      Abs_lam_pre_inverse Abs_P_lam_ilam_inverse
      CCTOR_lam_ilam.rep_eq super_lifted.rep_eq split: sum.splits)
   apply (subst lam_ilam.ctor; auto simp: noclash_lam_def set1_lam_pre_def set4_lam_pre_def map_lam_pre_def
      Abs_lam_pre_inverse Abs_P_lam_ilam_inverse
      CCTOR_lam_ilam.rep_eq super_lifted.rep_eq split: sum.splits)
  apply (subst lam_ilam.ctor; auto simp: noclash_lam_def set2_lam_pre_def set4_lam_pre_def map_lam_pre_def
      Abs_lam_pre_inverse Abs_P_lam_ilam_inverse
      CCTOR_lam_ilam.rep_eq super_lifted.rep_eq split: sum.splits)
  done

lemma ifv_subset: "ifv (\<lbrakk>M\<rbrakk>a) \<subseteq> {x. \<exists>y b. y \<in> fv M \<and> rev a \<le> rev b \<and> x = get_cinfset \<lbrace>y\<rbrace> (list_encode b)}"
  apply (induct M arbitrary: a)
    apply (auto simp: in_image_cinfmset NATS_cinfmset_UNIV)
    apply (smt (verit, ccfv_threshold) Prefix_Order.prefixI dual_order.trans in_mono mem_Collect_eq rev.simps(2))
   apply (smt (verit, ccfv_threshold) Prefix_Order.prefixI dual_order.trans in_mono mem_Collect_eq rev.simps(2))
  using get_cinfset_in by blast

lemma ifv_lam_ilam_disjoint:
  fixes M N :: "'a :: cinf lam"
  assumes "\<not>rev a \<le> rev a'" "\<not>rev a' \<le> rev a"
  shows "ifv (\<lbrakk>M\<rbrakk>a) \<inter> ifv (\<lbrakk>N\<rbrakk>a') = {}"
  apply (auto dest!: set_mp[OF ifv_subset])
  subgoal for x y b b'
    by (metis apply_super_eqI assms get_cinfset_in get_cinfset_inverse less_eq_list_def list_encode_inverse prefix_same_cases super_lifted.rep_eq)
  done
*)

lemma Abs_inject: "(Abs x e = Abs x' e') = (\<exists>f :: 'a \<Rightarrow> 'a. bij f \<and> |supp f| <o |UNIV::'a :: var_lam_pre set|
  \<and> id_on (fv (Abs x e)) f \<and> f x = x' \<and> vvsubst f e = e')"
  unfolding lam.set
  unfolding Abs_def lam.TT_injects0 map_lam_pre_def comp_def Abs_lam_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_lam_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_lam_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_lam_pre_def
    Un_empty_right UN_single
  apply (auto simp: lam_vvsubst_rrename)
  done

lemma Var_inject[simp]: "(Var x = Var x') = (x = x')"
  unfolding lam.set
  unfolding Var_def lam.TT_injects0 map_lam_pre_def comp_def Abs_lam_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_lam_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_lam_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_lam_pre_def
    Un_empty_right UN_single
  apply (auto simp: lam_vvsubst_rrename id_def[symmetric] cinfmset.map_id supp_id_bound intro!: exI[of _ id])
  done

lemma App_inject[simp]: "(App t U = App t' U') = (t = t' \<and> U = U')"
  unfolding lam.set
  unfolding App_def lam.TT_injects0 map_lam_pre_def comp_def Abs_lam_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_lam_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_lam_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_lam_pre_def
    Un_empty_right UN_single
  apply (auto simp: lam_vvsubst_rrename id_def[symmetric] cinfmset.map_id supp_id_bound intro!: exI[of _ id])
  done


(* *)

term iVar

inductive affine where
 iVar: "affine (iVar x)"
|iAbs: "affine t \<Longrightarrow> sdistinct xx \<Longrightarrow> affine (iAbs xx t)"
|iApp: 
"affine t \<Longrightarrow>
 (\<forall>u. u \<in> sset uu \<longrightarrow> affine u \<and> ifv t \<inter> ifv u = {}) \<Longrightarrow>
 (\<forall>u u'. u \<in> sset uu \<and> u' \<in> sset uu \<and> u \<noteq> u' \<longrightarrow> ifv u \<inter> ifv u' = {}) 
 \<Longrightarrow>
 affine (iApp t uu)"


consts super :: "var stream stream"

inductive uniform where
  "uniform (iVar x)"
| "uniform t \<Longrightarrow> uniform (iAbs \<lbrace>xx\<rbrace> t)"
| "uniform t \<Longrightarrow> \<forall>u. u \<in>#\<in> uu \<longrightarrow> uniform u \<Longrightarrow>
   \<forall>u u'. u \<in>#\<in> uu \<longrightarrow> u' \<in>#\<in> uu \<longrightarrow> u \<noteq> u' \<longrightarrow>
   u = u' \<Longrightarrow>
   uniform (iApp t uu)"

end
