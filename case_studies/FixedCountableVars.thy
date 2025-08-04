theory FixedCountableVars
imports "HOL-Cardinals.Cardinals" "HOL-Library.Infinite_Typeclass" "Prelim.Card_Prelim" "Binders.Classes"
begin

(* We take a countably infinite number of variables *)

hide_type var
datatype var = Variable nat

lemma bij_Variable: "bij Variable"
by (metis bijI' var.exhaust var.inject)

lemma card_var: "|UNIV::var set| =o natLeq"
using bij_Variable card_of_nat card_of_ordIso ordIso_symmetric ordIso_transitive by blast

lemma infinite_var: "infinite (UNIV::var set)"
using bij_Variable bij_betw_finite by blast

lemma regularCard_var: "regularCard |UNIV::var set|"
using card_var natLeq_Cinfinite ordIso_symmetric regularCard_natLeq regularCard_ordIso by blast

instantiation var :: var begin
instance apply standard
  using Field_natLeq infinite_iff_card_of_nat infinite_var regularCard_var by auto
end

lemma finite_iff_le_card_var: "finite A \<longleftrightarrow> |A| <o |UNIV::var set|"
by (meson card_of_Well_order card_of_ordLeq_finite card_var
finite_iff_ordLess_natLeq infinite_var ordLess_or_ordLeq ordLess_ordIso_trans)

lemma finite_card_var: "finite A \<Longrightarrow> |A| <o |UNIV::var set|"
using finite_iff_le_card_var by blast

lemma finite_exists_finite_var:
assumes "finite (A::var set)"
shows "\<exists>B. B \<inter> A = {} \<and> finite B \<and> card B = n"
proof-
  obtain B' where B': "B' \<inter> A = {}" and iB': "infinite B'"
  by (metis Diff_disjoint assms finite_Diff2 inf_commute infinite_var)
  obtain B where "B \<subseteq> B' \<and> finite B \<and> card B = n"
  using iB' by (meson infinite_arbitrarily_large)
  thus ?thesis using B' by auto
qed

lemma finite_exists_list_var:
assumes "finite (A::var set)"
shows "\<exists>xs. set xs \<inter> A = {} \<and> distinct xs \<and> length xs = n"
by (metis assms card_set distinct_remdups finite_distinct_list finite_exists_finite_var set_remdups)

lemma exists_var:
assumes "finite (X::var set)"
shows "\<exists>x. x \<notin> X"
by (simp add: assms ex_new_if_finite infinite_var)


(* *)

definition sw :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" where
"sw x y z \<equiv> if x = y then z else if x = z then y else x"

lemma sw_eqL[simp]: "\<And> x y z. sw x x y = y"
and sw_eqR[simp]: "\<And> x y z. sw x y x = y"
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

definition "sb a x y \<equiv> if a = y then x else a"

end