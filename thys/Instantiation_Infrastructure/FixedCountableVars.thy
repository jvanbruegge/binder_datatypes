theory FixedCountableVars
imports "HOL-Cardinals.Cardinals"  
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

end