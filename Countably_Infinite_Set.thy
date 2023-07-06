theory Countably_Infinite_Set
  imports
    "thys/MRBNF_Composition"
    "HOL-Library.Countable_Set_Type"
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

(*countably infinite set*)
typedef 'a :: infinite_regular cinfset = "{X :: 'a set. infinite X \<and> countable X}"
  morphisms set_cinfset Abs_cinfset
  using infinite_countable_subset'[OF infinite] by auto

abbreviation in_cinfset  ("(_/ \<in>\<in> _)" [51, 51] 50) where
  "x \<in>\<in> X \<equiv> x \<in> set_cinfset X"

setup_lifting type_definition_cinfset

lift_definition image_cinfset :: "('a :: infinite_regular \<Rightarrow> 'a) \<Rightarrow> 'a cinfset \<Rightarrow> 'a cinfset" is
  "\<lambda>f X. if inj_on f X then f ` X else X"
  by (auto simp: finite_image_iff)

mrbnf "'a ::infinite_regular cinfset"
  map: image_cinfset
  sets: bound: set_cinfset
  bd: "card_suc natLeq"
  var_class: infinite_regular
  subgoal by (rule ext, transfer) simp
  subgoal by (rule ext, transfer) (simp add: image_comp bij_is_inj inj_on_subset[OF _ subset_UNIV])
  subgoal by transfer (simp add: image_comp bij_is_inj inj_on_subset[OF _ subset_UNIV])
  subgoal by (rule ext, transfer) (simp add: image_comp bij_is_inj inj_on_subset[OF _ subset_UNIV])
  subgoal by (rule infinite_regular_card_order_card_suc[OF natLeq_card_order natLeq_Cinfinite])
  subgoal
    apply (rule card_suc_greater_set[OF natLeq_card_order])
    apply transfer
    apply (simp flip: countable_card_le_natLeq)
    done
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done

lift_definition idx_cinfset :: "'a :: infinite_regular cinfset \<Rightarrow> 'a \<Rightarrow> nat" is "to_nat_on" .

lift_definition get_cinfset :: "'a :: infinite_regular cinfset \<Rightarrow> nat \<Rightarrow> 'a" is "from_nat_into" .

lemma bij_betw_idx_cinfset: "bij_betw (idx_cinfset S) (set_cinfset S) UNIV"
  by transfer (simp add: to_nat_on_infinite)

lemma bij_betw_get_cinfset: "bij_betw (get_cinfset S) UNIV (set_cinfset S)"
  by transfer (simp add: bij_betw_from_nat_into)

lemma surj_idx_cinfset: "surj (idx_cinfset S)"
  by (meson bij_betw_idx_cinfset bij_betw_imp_surj)

lemma inj_get_cinfset: "inj (get_cinfset S)"
  by (metis bij_betw_def bij_betw_get_cinfset)

lemma get_cinfset_in: "get_cinfset S n \<in>\<in> S"
  by (metis bij_betw_def bij_betw_get_cinfset rangeI)

lemma get_cinfset_inverse: "idx_cinfset S (get_cinfset S n) = n"
  by transfer auto

lemma idx_cinfset_inverse: "x \<in>\<in> S \<Longrightarrow> get_cinfset S (idx_cinfset S x) = x"
  by transfer auto

end