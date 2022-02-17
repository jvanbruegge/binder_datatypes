theory MRBNF_Composition
  imports Prelim
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal
begin

declare [[bnf_internals]]
datatype (setF1_F: 'a, setF2_F: 'a', setL3_F: 'x, setB4_F: 'b, setB5_F: 'b', setL6_F: 'c, setL7_F: 'd, setL8_F: 'e, setL9_F: 'f) F_raw =
  E "'x + 'a + ('a' * 'b') * 'c * 'd + 'a' * 'f"
  for map: map_F rel: rel_F
type_synonym ('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F = "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F_raw"

datatype (setF1_F': 'a, setF2_F': 'a', setL3_F': 'x, setB4_F': 'b, setL5_F': 'c, setL6_F': 'd) F_raw' =
  E "'x + 'a + ('a' * 'b) * 'c * 'd + 'a"
  for map: map_F' rel: rel_F'
type_synonym ('a, 'a', 'x, 'b, 'c, 'd) F' = "('a, 'a', 'x, 'b, 'c, 'd) F_raw'"

datatype (setF1_G: 'a, setF2_G: 'a', setL3_G: 'y, setB4_G: 'b, setB5_G: 'b', setL6_G: 'g) G_raw =
  E "'y + 'a + ('a' * 'b') * 'y * 'g + 'a' * 'g"
  for map: map_G rel: rel_G
type_synonym ('a, 'a', 'y, 'b, 'b', 'g) G = "('a, 'a', 'y, 'b, 'b', 'g) G_raw"

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

end
