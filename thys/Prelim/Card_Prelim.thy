theory Card_Prelim
  imports "HOL-Cardinals.Cardinals" "HOL-Library.Countable_Set_Type" "HOL-Library.Infinite_Typeclass"
begin

lemma regularCard_Un:
assumes "Card_order r" and "cinfinite r" and "regularCard r"
 and "|A1| <o r" and "|A2| <o r"
shows "|A1 \<union> A2| <o r"
  using assms card_of_Un_ordLess_infinite_Field cinfinite_def by blast

lemma regularCard_UNION:
assumes "Card_order r" "cinfinite r" "regularCard r"
and "|I| <o r" "\<And>i. i \<in> I \<Longrightarrow> |A i| <o r"
shows "|\<Union>i\<in>I. A i| <o r"
  using assms cinfinite_def regularCard_stable stable_UNION by blast

lemma cardSuc_ordLeq_pow:
  assumes "Card_order (k:: 'b rel)"
  shows "cardSuc k \<le>o |UNIV:: 'b set set|"
by (intro cardSuc_least) (auto simp : assms cardSuc_ordLess_ordLeq)

lemma bij_card_of_ordIso:
  assumes "bij f" shows "|f ` A| =o |A|"
proof-
  have "bij_betw f A (f ` A)" using assms unfolding bij_def bij_betw_def inj_on_def surj_def by auto
  thus ?thesis
  using card_of_ordIso bij_betw_inv by blast
qed

lemma type_definition_bij_betw_Rep: "type_definition Rep Abs A \<Longrightarrow> bij_betw Rep UNIV A"
  by (metis injI inj_on_imp_bij_betw type_definition.Rep_inverse type_definition.Rep_range)

lemma type_definition_bij_betw_Abs: "type_definition Rep Abs A \<Longrightarrow> bij_betw Abs A UNIV"
  by (metis (no_types) bij_betw_def inj_onI type_definition.Abs_image type_definition.Abs_inject)

lemma type_definition_card_UNIV:
  fixes Rep :: "'a \<Rightarrow> 'r" and Abs :: "'r \<Rightarrow> 'a" and X :: "'r set"
  assumes "type_definition Rep Abs A"
  shows " |A| =o |UNIV :: 'a set|"
  by (rule card_of_ordIsoI[OF type_definition_bij_betw_Abs[OF assms]])

lemma Cinfinite_card_trans: "Cinfinite r \<Longrightarrow> r \<le>o |q| \<Longrightarrow> Cinfinite |q|"
  using cinfinite_mono card_of_Card_order by blast

lemma le_card_ivar: "natLeq <o cardSuc natLeq"
using cardSuc_greater natLeq_Card_order by blast

(*
lemma countable_iff_lq_natLeq: "countable A \<longleftrightarrow> |A| \<le>o natLeq"
unfolding countable_def
by (metis Field_card_of UNIV_I card_of_mono2 card_of_nat card_of_ordLeq ordLeq_ordIso_trans subsetI)
*)

(* *)

end