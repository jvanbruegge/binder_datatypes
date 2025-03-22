theory Swapping
  imports "Prelim.Prelim"
begin

definition swap :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a)" (infix "(\<leftrightarrow>)" 60) where
  "swap a b \<equiv> \<lambda>x. if x = a then b else if x = b then a else x"

lemma bij_swap[simp]: "bij (a \<leftrightarrow> b)"
  by (simp add: involuntory_imp_bij swap_def)

lemma supp_swap: "supp (a \<leftrightarrow> b) \<subseteq> {a, b}"
  by (metis insert_iff not_in_supp_alt subsetI swap_def)

lemma supp_swap_bound[simp]: "infinite (UNIV::'a set) \<Longrightarrow> |supp (a \<leftrightarrow> b)| <o |UNIV::'a set|"
  using card_of_subset_bound[OF supp_swap] by (metis finite.emptyI finite_insert finite_ordLess_infinite2)

lemma swap_simps[simp]: "(a \<leftrightarrow> b) a = b" "(a \<leftrightarrow> b) b = a"
  "x \<noteq> a \<Longrightarrow> x \<noteq> b \<Longrightarrow> (a \<leftrightarrow> b) x = x"
  unfolding swap_def by auto

lemma swap_sym: "(a \<leftrightarrow> b) = (b \<leftrightarrow> a)"
  unfolding swap_def by force

lemma swap_inv[simp]: "inv (a \<leftrightarrow> b) = (a \<leftrightarrow> b)"
  by (smt (verit, ccfv_threshold) inv_equality swap_simps(1,2,3))
lemma swap_same[simp]: "(a \<leftrightarrow> a) x = x"
  by (simp add: swap_def)

lemma swap_apply_fresh_bij: "bij f \<Longrightarrow> (z \<noteq> x \<Longrightarrow> f z = z) \<Longrightarrow> z \<noteq> y \<Longrightarrow> (f x \<leftrightarrow> y) (f z) = (x \<leftrightarrow> y) z"
  by (simp add: bij_implies_inject swap_def)

lemma swap_apply_fresh_bij2: "bij f \<Longrightarrow> (z \<noteq> x \<Longrightarrow> f z = z) \<Longrightarrow> (x \<leftrightarrow> f x) z = f z"
  by (metis inv_simp1 swap_def)

lemma id_on_image_Diff: "bij f \<Longrightarrow> id_on (A - {x}) f \<Longrightarrow> f x \<in> A \<Longrightarrow> f x = x"
  by (metis (full_types) DiffI id_onD inv_simp1 singletonD)
lemma id_on_swap: "y \<notin> A \<or> x = y \<Longrightarrow> id_on (A - {x}) (x \<leftrightarrow> y)"
  by (metis Diff_iff id_onI singletonI swap_def)

end