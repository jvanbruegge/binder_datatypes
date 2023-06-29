theory General_Customization
imports "MRBNF_Recursor"
begin

lemmas supp_inv_bound[simp]
lemmas bij_swap[simp]
lemmas supp_id_bound[simp]

lemma fvars_subset_id_on: "supp f \<subseteq> A \<Longrightarrow> id_on (B - A) f"
  unfolding supp_def id_on_def by blast
(* lemma finite_singleton: "finite {x}" by blast *)


end