theory MRBNF_Composition
  imports Prelim
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal
begin

ML_file \<open>../Tools/mrbnf_util.ML\<close>
ML_file \<open>../Tools/mrbnf_def_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_def.ML\<close>

local_setup \<open>snd o MRBNF_Def.register_bnf_as_mrbnf (SOME "BNF_Composition.ID") (BNF_Comp.ID_bnf)\<close>
local_setup \<open>snd o MRBNF_Def.register_bnf_as_mrbnf (SOME "BNF_Composition.DEADID") (BNF_Comp.DEADID_bnf)\<close>

lemma Grp_UNIV_def: "Grp f = (\<lambda>x. (=) (f x))"
  unfolding Grp_def by auto

lemma Cinfinite_gt_empty: "Cinfinite r \<Longrightarrow> |{}| <o r"
  by (simp add: cinfinite_def finite_ordLess_infinite)

lemma regularCard_UNION':
  assumes "Cinfinite r" "regularCard r" and "|I| <o r" "\<And>i. i \<in> I \<Longrightarrow> |A i| <o r"
  shows "|\<Union>i\<in>I. A i| <o r"
  using assms cinfinite_def regularCard_stable stable_UNION by blast

lemma comp_single_regular_set_bd:
  fixes fbd :: "('a \<times> 'a) set" and gbd :: "('b \<times> 'b) set"
  assumes "infinite_regular_card_order fbd" "infinite_regular_card_order gbd" and
    fset_bd: "\<And>x. |fset x| <o fbd" and
    gset_bd: "\<And>x. |gset x| <o gbd"
  shows "|\<Union>(fset ` gset x)| <o gbd *c fbd"
proof (cases "fbd \<le>o gbd")
  case True
  then have "|fset x| <o gbd" for x
    using fset_bd ordLess_ordLeq_trans by blast
  then have "|\<Union>(fset ` gset x)| <o gbd"
    using assms(2) infinite_regular_card_order.Cinfinite infinite_regular_card_order.regularCard
    by (auto intro!: regularCard_UNION'[OF _ _ gset_bd])
  then show ?thesis
    using True assms(1,2) infinite_regular_card_order.Cinfinite infinite_regular_card_order.Cnotzero
    by (auto elim!: ordLess_ordIso_trans intro!: cprod_infinite1'[THEN ordIso_symmetric])
next
  case False
  then have "gbd \<le>o fbd"
    by (meson fset_bd gset_bd ordLeq_Well_order_simp ordLess_imp_ordLeq ordLess_or_ordLeq)
  then have "|gset x| <o fbd" for x
    using gset_bd ordLess_ordLeq_trans by blast
  then have "|\<Union>(fset ` gset x)| <o fbd"
    using assms(1) infinite_regular_card_order.Cinfinite infinite_regular_card_order.regularCard
    by (auto intro!: regularCard_UNION'[OF _ _ _ fset_bd])
  then show ?thesis
    using \<open>gbd \<le>o fbd\<close> assms(1,2) infinite_regular_card_order.Cinfinite infinite_regular_card_order.Cnotzero
    by (auto elim!: ordLess_ordIso_trans intro!: cprod_infinite2'[THEN ordIso_symmetric])
qed

lemma mrbnf_type_copy_set_bd: "(\<And>y. |S y| <o bd) \<Longrightarrow> |(S \<circ> Rep) x| <o bd"
  by auto
lemma Grp_Rep: "type_definition Rep Abs top \<Longrightarrow> type_definition Rep2 Abs2 top \<Longrightarrow>
  ((BNF_Def.Grp (Collect P) f)\<inverse>\<inverse> OO BNF_Def.Grp (Collect P) g) (Rep x) (Rep2 y) =
  ((BNF_Def.Grp (Collect P) (Abs \<circ> f))\<inverse>\<inverse> OO BNF_Def.Grp (Collect P) (Abs2 \<circ> g)) x y"
  unfolding relcompp_apply Grp_def conversep_def
  by (metis comp_def iso_tuple_UNIV_I type_definition_def)
lemma type_copy_vimage2p_Grp_Rep_id: "type_definition Rep Abs UNIV \<Longrightarrow> BNF_Def.vimage2p id Rep (BNF_Def.Grp (Collect P) h) = BNF_Def.Grp {x. P x} (Abs \<circ> h)"
  using type_copy_vimage2p_Grp_Rep[of _ _ id]
  by auto
lemma type_definition_id: "type_definition id id top"
  unfolding type_definition_def
  by simp

lemma image_single: "{f x} = f ` {x}"
  by simp

ML_file \<open>../Tools/mrbnf_comp_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_comp.ML\<close>

end
