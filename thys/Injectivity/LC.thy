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

definition swap :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "swap xs ys \<equiv> (SOME f. f \<circ> f = id \<and> supp f = set xs \<union> set ys \<and> map f xs = ys)"

lemma swap_ex:
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

corollary swap:
 assumes "bij f" "map f xs = ys" "set xs \<inter> set ys = {}"
 shows "swap xs ys \<circ> swap xs ys = id" "supp (swap xs ys) = set xs \<union> set ys" "map (swap xs ys) xs = ys"
proof -
  have "swap xs ys \<circ> swap xs ys = id \<and> supp (swap xs ys) = set xs \<union> set ys \<and> map (swap xs ys) xs = ys"
    apply (unfold swap_def)
    apply (rule someI2_ex[of "\<lambda>f. f \<circ> f = id \<and> supp f = set xs \<union> set ys \<and> map f xs = ys"])
     apply (rule swap_ex[OF assms])
    by assumption
  then show "swap xs ys \<circ> swap xs ys = id" "supp (swap xs ys) = set xs \<union> set ys" "map (swap xs ys) xs = ys"
    by auto
qed

definition "sameShape (xs::'a list) (ys::'a list) \<equiv> list_all2 (\<lambda>_ _. True) xs ys"

hide_const linear
definition "linear xs \<equiv> \<forall>ys. sameShape xs ys \<longrightarrow> (\<exists>f. map f xs = ys)"

(* generic for free BNFs: *)
lemma strong_cong: "map f xs = map g xs \<Longrightarrow> x \<in>  set xs \<Longrightarrow> f x = g x"
by fastforce

definition "match xs ys \<equiv> SOME f. map f xs = ys"

lemma match:
"linear xs \<Longrightarrow> sameShape xs ys \<Longrightarrow> map (match xs ys) xs = ys"
  apply (unfold match_def)
  apply (rule someI2_ex[of "\<lambda>f. map f xs = ys"])
   apply (unfold linear_def)
  apply (erule allE)
   apply (erule impE)
    apply assumption+
  done

lemma match_unique:
assumes "linear xs" "sameShape xs ys" "map f xs = ys" "x \<in> set xs"
shows "f x = match xs ys x" 
  using match[OF assms(1,2), THEN sym] apply(subst (asm) assms(3)[symmetric]) 
  using assms(4) strong_cong by auto

lemma "sameShape xs ys \<Longrightarrow> linear xs \<Longrightarrow> linear ys
  \<Longrightarrow> bij_betw (match xs ys) (set xs) (set ys)"

corollary linear_swap:
  assumes "list_all2 (\<lambda>_ _. True) xs ys" "linear xs" "set xs \<inter> set ys = {}"
  shows "swap xs ys \<circ> swap xs ys = id" "supp (swap xs ys) = set xs \<union> set ys" "map (swap xs ys) xs = ys"
proof -
  obtain f where f: "bij f" "map f xs = ys"
    apply (atomize_elim)
    using assms(1-3) unfolding linear_def
    apply -
    apply (erule allE)
    apply (erule impE)
     apply assumption
    apply (erule exE)
    apply (erule conjE)+
    apply hypsubst
    sorry
  then show "swap xs ys \<circ> swap xs ys = id" "supp (swap xs ys) = set xs \<union> set ys" "map (swap xs ys) xs = ys"
    using swap[OF f assms(4)] by auto
qed

lemma Lam_Inj: "Lam xs t = Lam xs' t' \<longleftrightarrow> (\<exists>ys t''.
  set xs \<inter> set ys = {} \<and> set xs' \<inter> set ys = {} \<and>
  swap xs ys \<circ> swap xs ys = id
  \<and> supp (swap xs ys) = set xs \<union> set ys \<and>
  map (swap xs ys) xs = ys
  \<and> map (swap xs' ys) xs' = ys
  \<and> permute_term (swap xs ys) t = t'' \<and> permute_term (swap xs' ys) t' = t''
)"

end
