theory Support
  imports "Prelim.Prelim"
begin

lemma notin_supp: "x \<notin> supp f \<Longrightarrow> f x = x"
  unfolding supp_def by blast

definition SSupp :: "('a \<Rightarrow> 't) \<Rightarrow> ('a \<Rightarrow> 't) \<Rightarrow> 'a set" where
  "SSupp Inj \<equiv> \<lambda>f. { a. f a \<noteq> Inj a }"

definition IImsupp :: "('a \<Rightarrow> 't) \<Rightarrow> ('t \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 't) \<Rightarrow> 'b set" where
  "IImsupp Inj Vr \<equiv> \<lambda>\<rho>. (\<Union>a\<in>SSupp Inj \<rho>. Vr (\<rho> a))"

lemma SSupp_Inj[simp]: "SSupp Inj Inj = {}"
  unfolding SSupp_def by simp

lemma IImsupp_Inj[simp]: "IImsupp Inj Vr Inj = {}"
  unfolding IImsupp_def by simp

lemma SSupp_Inj_bound[simp]: "|SSupp Inj Inj| <o |UNIV::'a set|"
  by simp

lemma SSupp_comp_subset: "SSupp Inj (g \<circ> f) \<subseteq> SSupp Inj g \<union> supp f"
proof (rule subsetI, unfold SSupp_def mem_Collect_eq Un_iff comp_apply)
  fix x
  assume a: "g (f x) \<noteq> Inj x"
  show "g x \<noteq> Inj x \<or> x \<in> supp f"
  proof (cases "x \<in> supp f")
    case False
    then show ?thesis using a notin_supp by metis
  qed blast
qed

lemma SSupp_comp_bound: "infinite (UNIV::'a set) \<Longrightarrow> |SSupp Inj g| <o |UNIV::'a set| \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> |SSupp Inj (g \<circ> f)| <o |UNIV::'a set|"
  using card_of_subset_bound[OF SSupp_comp_subset] card_of_Un_ordLess_infinite by fast

end