theory FixedUncountableVars
imports "HOL-Cardinals.Cardinals" "HOL-Library.Countable_Set" (* "thys/MRBNF_Recursor" *)
begin

(* We take a number of suc-Aleph0 variables *)

hide_type var
typedef var = "{x::nat set. x \<in> Field (cardSuc natLeq)}" 
 by simp (metis Field_cardSuc_not_empty Field_natLeq all_not_in_conv natLeq_card_order)

lemma bij_betw_Rep_var: "bij_betw Rep_var (UNIV::var set) (Field (cardSuc natLeq))"
by (smt (verit, best) Abs_var_inverse Rep_var Rep_var_inject UNIV_I bij_betwI' mem_Collect_eq)

lemma card_var: "|UNIV::var set| =o cardSuc natLeq"
proof-
  have "|UNIV::var set| =o |Field (cardSuc natLeq)|"
  using bij_betw_Rep_var card_of_ordIso by auto
  also have "|Field (cardSuc natLeq)| =o cardSuc natLeq" 
    by (simp add: natLeq_Card_order)
  finally show ?thesis .
qed

lemma le_card_var: "natLeq <o cardSuc natLeq"
using cardSuc_greater natLeq_Card_order by blast

lemma infinite_var: "infinite (UNIV::var set)" 
using Field_natLeq bij_betw_Rep_var bij_betw_finite natLeq_Card_order by fastforce

lemma regularCard_var: "regularCard |UNIV::var set|" 
using Cinfinite_cardSuc card_var natLeq_Cinfinite ordIso_symmetric 
regularCard_cardSuc regularCard_ordIso by blast

lemma countable_iff_lq_natLeq: "countable A \<longleftrightarrow> |A| \<le>o natLeq"
unfolding countable_def 
by (metis Field_card_of UNIV_I card_of_mono2 card_of_nat card_of_ordLeq ordLeq_ordIso_trans subsetI)

lemma countable_iff_le_card_var: "countable A \<longleftrightarrow> |A| <o |UNIV::var set|"
proof-
  have "countable A \<longleftrightarrow> |A| <o cardSuc natLeq"
  unfolding countable_iff_lq_natLeq 
  by (simp add: natLeq_Card_order)
  also have "\<dots> \<longleftrightarrow> |A| <o |UNIV::var set|" 
    by (meson card_var not_ordLess_ordIso ordIso_iff_ordLeq ordLeq_iff_ordLess_or_ordIso ordLeq_transitive)
  finally show ?thesis .
qed

lemma countable_card_var: "countable A \<Longrightarrow> |A| <o |UNIV::var set|"
using countable_iff_le_card_var by auto

lemma finite_card_var: "finite A \<Longrightarrow> |A| <o |UNIV::var set|"
using infinite_var by auto

lemma countable_exists_countable_var: 
assumes "countable (A::var set)"
shows "\<exists>B. B \<inter> A = {} \<and> infinite B"
apply(rule exI[of _ "-A"])
by simp (metis Compl_eq_Diff_UNIV assms card_of_Well_order countable_card_var 
not_ordLeq_iff_ordLess ordLeq_iff_ordLess_or_ordIso uncountable_infinite uncountable_minus_countable)

lemma countable_exists_finite_var: 
assumes "countable (A::var set)"
shows "\<exists>B. B \<inter> A = {} \<and> finite B \<and> card B = n"
proof-
  obtain B' where B': "B' \<inter> A = {}" and iB': "infinite B'"
  using countable_exists_countable_var[OF assms] by auto
  obtain B where "B \<subseteq> B' \<and> finite B \<and> card B = n"
  using iB' by (meson infinite_arbitrarily_large)
  thus ?thesis using B' by auto
qed

lemma countable_exists_list_var: 
assumes "countable (A::var set)"
shows "\<exists>xs. set xs \<inter> A = {} \<and> distinct xs \<and> length xs = n"
by (metis assms countable_exists_finite_var distinct_remdups finite_list length_remdups_card_conv set_remdups)

lemma exists_var: 
assumes "countable (X::var set)"
shows "\<exists>x. x \<notin> X"
by (metis Int_absorb assms countable_exists_countable_var disjoint_iff finite.emptyI)

lemma finite_exists_var:
assumes "finite X"
shows "\<exists> x::var. x \<notin> X"
by (simp add: assms ex_new_if_finite infinite_var)


end