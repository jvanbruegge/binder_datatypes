theory LC
  imports
  "HOL-Library.FSet"
  "Prelim.FixedCountableVars"
  "Prelim.Swapping_vs_Permutation"
  "Binders.General_Customization"
  "Prelim.More_List"
begin

(* DATATYPE DECLARTION  *)

declare [[mrbnf_internals]]
binder_datatype 'a "term" =
  Var 'a
| App "'a term" "'a term"
| Lam "(x::'a) list" t::"'a term" binds x in t
for
  vvsubst: vvsubst
  tvsubst: tvsubst
print_theorems

lemma Lam_Inj_current: "Lam xs t = Lam xs' t' \<longleftrightarrow> (\<exists>f. bij (f::'a::var \<Rightarrow> 'a) \<and>
  |supp f| <o |UNIV::'a set| \<and> map f xs = xs' \<and> permute_term f t = t')"
  sorry

definition swap_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "swap_list xs ys \<equiv> (SOME f. f \<circ> f = id \<and> supp f = set xs \<union> set ys \<and> map f xs = ys)"

lemma swap_list_ex:
  assumes "bij f" "map f xs = ys" "set xs \<inter> set ys = {}"
  shows "\<exists>f. f \<circ> f = id \<and> supp f = set xs \<union> set ys \<and> map f xs = ys"
proof -
  define g where "g \<equiv> \<lambda>x. if x \<in> set xs then f x else (if x \<in> set ys then inv f x else x)"

  have "g \<circ> g = id"
    using assms
    apply (unfold g_def)
  apply (rule ext)
     apply (rule trans[OF comp_apply])
     apply (rule case_split)
      apply (subst if_P)
       apply assumption
      apply (unfold if_P if_not_P)
      apply (subst if_not_P)
       apply (drule arg_cong[of _ _ set])
       apply (unfold list.set_map)[1]
       apply (auto simp: image_def)[1]
      apply (rule trans[OF if_P])
    by auto
  moreover have "supp g = set xs \<union> set ys"
    apply (unfold g_def supp_def set_eq_iff)
    by (smt (verit, ccfv_threshold) IntI Un_iff assms(1,2,3) bij_inv_eq_iff empty_iff image_iff list.set_map mem_Collect_eq)
  moreover have "map g xs = ys"
    using assms apply (unfold g_def) by auto
  ultimately show ?thesis by blast
qed

corollary swap_list:
 assumes "bij f" "map f xs = ys" "set xs \<inter> set ys = {}"
 shows "swap_list xs ys \<circ> swap_list xs ys = id" "supp (swap_list xs ys) = set xs \<union> set ys" "map (swap_list xs ys) xs = ys"
proof -
  have "swap_list xs ys \<circ> swap_list xs ys = id \<and> supp (swap_list xs ys) = set xs \<union> set ys \<and> map (swap_list xs ys) xs = ys"
    apply (unfold swap_list_def)
    apply (rule someI2_ex[of "\<lambda>f. f \<circ> f = id \<and> supp f = set xs \<union> set ys \<and> map f xs = ys"])
     apply (rule swap_list_ex[OF assms])
    by assumption
  then show "swap_list xs ys \<circ> swap_list xs ys = id" "supp (swap_list xs ys) = set xs \<union> set ys" "map (swap_list xs ys) xs = ys"
    by auto
qed

definition "linear_list (xs::'a list) \<equiv>
  \<forall>(ys::'a list). list_all2 (\<lambda>_ _. True) xs ys \<longrightarrow> (\<exists>f. map f xs = ys)"

definition "match_list xs ys \<equiv> SOME f. map f xs = ys"

lemma match_list:
  fixes xs ys::"'a list"
  shows "list_all2 (\<lambda>_ _. True) xs ys \<Longrightarrow> linear_list xs \<Longrightarrow> map (match_list xs ys) xs = ys"
  apply (unfold match_list_def)
  apply (rule someI2_ex[of "\<lambda>f. map f xs = ys"])
   apply (unfold linear_list_def)
  apply (erule allE)
   apply (erule impE)
    apply assumption+
  done

lemma "list_all2 (\<lambda>_ _. True) xs ys \<Longrightarrow> linear_list xs \<Longrightarrow> linear_list ys
  \<Longrightarrow> bij_betw (match_list xs ys) (set xs) (set ys)"

corollary linear_swap_list:
  assumes "list_all2 (\<lambda>_ _. True) xs ys" "linear_list xs" "set xs \<inter> set ys = {}"
  shows "swap_list xs ys \<circ> swap_list xs ys = id" "supp (swap_list xs ys) = set xs \<union> set ys" "map (swap_list xs ys) xs = ys"
proof -
  obtain f where f: "bij f" "map f xs = ys"
    apply (atomize_elim)
    using assms(1-3) unfolding linear_list_def
    apply -
    apply (erule allE)
    apply (erule impE)
     apply assumption
    apply (erule exE)
    apply (erule conjE)+
    apply hypsubst
    sorry
  then show "swap_list xs ys \<circ> swap_list xs ys = id" "supp (swap_list xs ys) = set xs \<union> set ys" "map (swap_list xs ys) xs = ys"
    using swap_list[OF f assms(4)] by auto
qed

lemma Lam_Inj: "Lam xs t = Lam xs' t' \<longleftrightarrow> (\<exists>ys t''.
  set xs \<inter> set ys = {} \<and> set xs' \<inter> set ys = {} \<and>
  swap_list xs ys \<circ> swap_list xs ys = id
  \<and> supp (swap_list xs ys) = set xs \<union> set ys \<and>
  map (swap_list xs ys) xs = ys
  \<and> map (swap_list xs' ys) xs' = ys
  \<and> permute_term (swap_list xs ys) t = t'' \<and> permute_term (swap_list xs' ys) t' = t''
)"

end
