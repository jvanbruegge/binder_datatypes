theory Card_Prelim
  imports "HOL-Cardinals.Cardinals"
begin

lemma card_of_Un_eq_Plus:
assumes "A \<inter> B = {}"
shows "|A \<union> B| =o |A <+> B|"
proof(rule card_of_ordIsoI)
  show "bij_betw (\<lambda> a. if a \<in> A then Inl a else Inr a) (A \<union> B) (A <+> B)"
    using assms unfolding bij_betw_def inj_on_def by auto
qed

lemma infinite_UNIV_card_of_minus:
  assumes i: "infinite (UNIV::'a set)" and b: "|B::'a set| <o |UNIV::'a set|"
  shows "|UNIV - B| =o |UNIV::'a set|"
  using card_of_Un_diff_infinite[OF assms] by auto

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

lemma regularCard_ordIso:
assumes  "k =o k'" and "Cinfinite k" and "regularCard k"
shows "regularCard k'"
proof-
  have "stable k" using assms cinfinite_def regularCard_stable by blast
  hence "stable k'" using assms stable_ordIso by blast
  thus ?thesis using assms cinfinite_def stable_regularCard
    using Cinfinite_cong by blast
qed

lemma regularCard_cardSuc: "Cinfinite k \<Longrightarrow> regularCard (cardSuc k)"
  by (rule infinite_cardSuc_regularCard) (auto simp: cinfinite_def)

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

end