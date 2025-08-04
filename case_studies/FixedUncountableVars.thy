theory FixedUncountableVars
imports "Prelim.Card_Prelim" 
begin

(* We take a number of suc-Aleph0 ivariables *)

typedef ivar = "{x::nat set. x \<in> Field (cardSuc natLeq)}"
 by simp (metis Field_cardSuc_not_empty Field_natLeq all_not_in_conv natLeq_card_order)

lemma bij_betw_Rep_ivar: "bij_betw Rep_ivar (UNIV::ivar set) (Field (cardSuc natLeq))"
by (smt (verit, best) Abs_ivar_inverse Rep_ivar Rep_ivar_inject UNIV_I bij_betwI' mem_Collect_eq)

lemma card_ivar: "|UNIV::ivar set| =o cardSuc natLeq"
proof-
  have "|UNIV::ivar set| =o |Field (cardSuc natLeq)|"
  using bij_betw_Rep_ivar card_of_ordIso by auto
  also have "|Field (cardSuc natLeq)| =o cardSuc natLeq"
    by (simp add: natLeq_Card_order)
  finally show ?thesis .
qed

lemma infinite_ivar: "infinite (UNIV::ivar set)"
using Field_natLeq bij_betw_Rep_ivar bij_betw_finite natLeq_Card_order by fastforce

lemma regularCard_ivar: "regularCard |UNIV::ivar set|"
using Cinfinite_cardSuc card_ivar natLeq_Cinfinite ordIso_symmetric
regularCard_cardSuc regularCard_ordIso by blast

lemma countable_iff_le_card_ivar: "countable A \<longleftrightarrow> |A| <o |UNIV::ivar set|"
proof-
  have "countable A \<longleftrightarrow> |A| <o cardSuc natLeq"
  unfolding countable_card_le_natLeq
  by (simp add: natLeq_Card_order)
  also have "\<dots> \<longleftrightarrow> |A| <o |UNIV::ivar set|"
    by (meson card_ivar not_ordLess_ordIso ordIso_iff_ordLeq ordLeq_iff_ordLess_or_ordIso ordLeq_transitive)
  finally show ?thesis .
qed

lemma countable_card_ivar: "countable A \<Longrightarrow> |A| <o |UNIV::ivar set|"
using countable_iff_le_card_ivar by auto

lemma finite_card_ivar: "finite A \<Longrightarrow> |A| <o |UNIV::ivar set|"
using infinite_ivar by auto

lemma countable_exists_countable_ivar:
assumes "countable (A::ivar set)"
shows "\<exists>B. B \<inter> A = {} \<and> infinite B"
apply(rule exI[of _ "-A"])
by simp (metis Compl_eq_Diff_UNIV assms card_of_Well_order countable_card_ivar
not_ordLeq_iff_ordLess ordLeq_iff_ordLess_or_ordIso uncountable_infinite uncountable_minus_countable)

lemma countable_exists_finite_ivar:
assumes "countable (A::ivar set)"
shows "\<exists>B. B \<inter> A = {} \<and> finite B \<and> card B = n"
proof-
  obtain B' where B': "B' \<inter> A = {}" and iB': "infinite B'"
  using countable_exists_countable_ivar[OF assms] by auto
  obtain B where "B \<subseteq> B' \<and> finite B \<and> card B = n"
  using iB' by (meson infinite_arbitrarily_large)
  thus ?thesis using B' by auto
qed

lemma countable_exists_list_ivar:
assumes "countable (A::ivar set)"
shows "\<exists>xs. set xs \<inter> A = {} \<and> distinct xs \<and> length xs = n"
by (metis assms countable_exists_finite_ivar distinct_remdups finite_list length_remdups_card_conv set_remdups)

lemma exists_ivar:
assumes "countable (X::ivar set)"
shows "\<exists>x. x \<notin> X"
by (metis Int_absorb assms countable_exists_countable_ivar disjoint_iff finite.emptyI)

lemma finite_exists_ivar:
assumes "finite X"
shows "\<exists> x::ivar. x \<notin> X"
by (simp add: assms ex_new_if_finite infinite_ivar)


(* *)

definition sw :: "ivar \<Rightarrow> ivar \<Rightarrow> ivar \<Rightarrow> ivar" where
"sw x y z \<equiv> if x = y then z else if x = z then y else x"

lemma sw_eqL[simp,intro!]: "\<And> x y z. sw x x y = y"
and sw_eqR[simp,intro!]: "\<And> x y z. sw x y x = y"
and sw_diff[simp]: "\<And> x y z. x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> sw x y z = x"
  unfolding sw_def by auto

lemma sw_sym: "sw x y z = sw x z y"
and sw_id[simp]: "sw x y y = x"
and sw_sw: "sw (sw x y z) y1 z1 = sw (sw x y1 z1) (sw y y1 z1) (sw z y1 z1)"
and sw_invol[simp]: "sw (sw x y z) y z = x"
  unfolding sw_def by auto

lemma sw_invol2: "sw (sw x y z) z y = x"
  by (simp add: sw_sym)

lemma sw_inj[iff]: "sw x z1 z2 = sw y z1 z2 \<longleftrightarrow> x = y"
  unfolding sw_def by auto

lemma sw_surj: "\<exists>y. x = sw y z1 z2"
  by (metis sw_invol)

(* *)

instantiation ivar :: infinite begin
instance by standard (rule infinite_ivar)
end 


end
