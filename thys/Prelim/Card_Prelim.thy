theory Card_Prelim
  imports "HOL-Cardinals.Cardinals" "HOL-Library.Countable_Set_Type" "HOL-Library.Infinite_Typeclass"
begin

lemma card_of_subset_bound: "\<lbrakk> B \<subseteq> A ; |A| <o x \<rbrakk> \<Longrightarrow> |B| <o x"
  using card_of_mono1 ordLeq_ordLess_trans by blast
lemma card_of_minus_bound: "|A| <o r \<Longrightarrow> |A - B| <o r"
  by (rule card_of_subset_bound[OF Diff_subset])

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

class covar =
  assumes large: "cardSuc natLeq \<le>o |UNIV::'a set|"
    and regular: "regularCard |UNIV::'a set|"

class var =
  assumes large: "|Field natLeq| \<le>o |UNIV::'a set|"
    and regular: "regularCard |UNIV::'a set|"

subclass (in covar) var
  apply standard
   apply (metis Field_natLeq infinite_iff_card_of_nat infinite_iff_natLeq_ordLeq le_card_ivar local.large ordLeq_transitive ordLess_imp_ordLeq)
  by (rule local.regular)

subclass (in var) infinite
  apply standard
  using Field_natLeq infinite_iff_card_of_nat local.large by auto

lemma (in var) UNIV_cinfinite: "cinfinite |UNIV::'a set|"
  using Field_natLeq cinfinite_def infinite_iff_card_of_nat local.large by fastforce

lemma (in infinite) Un_bound: "|A| <o |UNIV::'a set| \<Longrightarrow> |B| <o |UNIV::'a set| \<Longrightarrow> |A \<union> B| <o |UNIV::'a set|"
  using card_of_Un_ordLess_infinite local.infinite_UNIV by blast

lemma (in var) UN_bound: "|A| <o |UNIV::'a set| \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> |f x| <o |UNIV::'a set| )
  \<Longrightarrow> |\<Union>(f ` A)| <o |UNIV::'a set|"
  using card_of_Card_order card_of_UNION_ordLess_infinite_Field cinfinite_def local.UNIV_cinfinite local.regular regularCard_stable by blast

lemma (in var) large': "natLeq \<le>o |UNIV::'a set|"
  using infinite_iff_natLeq_ordLeq local.infinite_UNIV by blast

instantiation nat::var begin
  instance by standard (auto simp: stable_nat stable_regularCard)
end

lemma list_countable: "|UNIV::('a::finite) list set| =o natLeq"
  by (meson card_of_nat countableI_type countable_or_card_of infinite_UNIV_listI ordIso_transitive)

instantiation list :: (finite) var begin
instance
  apply standard
  using Field_natLeq infinite_UNIV infinite_iff_card_of_nat  apply auto[1]
  using list_countable natLeq_Cinfinite ordIso_symmetric regularCard_natLeq regularCard_ordIso by blast
end

end
