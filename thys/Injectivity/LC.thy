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

(* can also have generic proofs: *)
lemma sameShape_refl: "sameShape xs xs" 
  by (simp add: list.rel_refl sameShape_def)
lemma sameShape_sym: "sameShape xs ys \<Longrightarrow> sameShape ys xs" 
  by (simp add: list_all2_conv_all_nth sameShape_def)
lemma sameShape_trans: "sameShape xs ys \<Longrightarrow> sameShape ys zs \<Longrightarrow> sameShape xs zs" 
by (simp add: list_all2_conv_all_nth sameShape_def)

hide_const linear
definition "linear xs \<equiv> \<forall>ys. sameShape xs ys \<longrightarrow> (\<exists>f. map f xs = ys)"

(* generic for free BNFs: *)
lemma cong_rev: "map f xs = map g xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x = g x"
  by fastforce

lemma cong_rev_id: "map f xs = xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x = x"
  using cong_rev[of f xs id] by auto

lemma linear_imp: 
  assumes "linear xs" "sameShape xs ys"
  shows "\<exists>f. map f xs = ys \<and> (\<forall>x. x\<notin>set xs \<longrightarrow> f x = x)"
proof-
  obtain f where f: "map f xs = ys" using assms unfolding linear_def by auto
  define g where "g \<equiv> \<lambda>x. if x \<in> set xs then f x else x"
  show ?thesis apply(rule exI[of _ g])
    using f unfolding g_def by auto
qed

definition "match xs ys \<equiv> SOME f. map f xs = ys \<and> (\<forall>x. x\<notin>set xs \<longrightarrow> f x = x)"

lemma match:
"linear xs \<Longrightarrow> sameShape xs ys \<Longrightarrow> 
  map (match xs ys) xs = ys \<and> (\<forall>x. x\<notin>set xs \<longrightarrow> match xs ys x = x)"
  by (smt (verit, del_insts) linear_imp match_def someI_ex)

lemmas map_match = match[THEN conjunct1]
lemma not_set_match: "linear xs \<Longrightarrow> sameShape xs ys \<Longrightarrow> x\<notin>set xs \<Longrightarrow> match xs ys x = x"
  using match by auto

lemma match_unique:
assumes "linear xs" "sameShape xs ys" "map f xs = ys" "x \<in> set xs"
shows "f x = match xs ys x" 
  using map_match[OF assms(1,2), THEN sym] apply(subst (asm) assms(3)[symmetric]) 
  using assms(4) cong_rev by auto

lemma match_eq_id:
assumes "linear xs" "map f xs = xs" "x \<in> set xs"
shows "match xs xs x = x"  
by (metis assms(1,3) id_apply list.map_id0 match_unique sameShape_refl)

lemma image_match_set: 
assumes "sameShape xs ys" "linear xs"  
shows "match xs ys ` (set xs) = set ys"
  by (simp add: assms(1,2) image_set match)

lemma match_set: 
assumes "sameShape xs ys" "linear xs" "x \<in> set xs"
shows "match xs ys x \<in> set ys"
  using assms image_match_set by auto

lemma match_set_disj: 
assumes "sameShape xs ys" "linear xs" "set xs \<inter> set ys = {}" 
shows "match xs ys x \<in> set ys \<longleftrightarrow> x \<in> set xs"
  apply safe
  subgoal using not_set_match assms sledgehammer
  subgoal using match_set assms by metis .

lemma match_id: 
assumes "linear xs"  
shows "match xs xs = id"
  by (meson assms eq_id_iff match match_eq_id sameShape_refl)

lemma match_id2: 
assumes "linear xs"  
shows "match xs xs x = x" 
  by (simp add: assms match_id) 

lemma match_id: 
assumes l: "linear xs" "linear ys" and s: "sameShape xs ys" "sameShape ys zs"
shows "match ys zs o match xs ys = match xs zs"
proof(rule ext)
  have ss: "sameShape xs zs"  
    using s(1,2) sameShape_trans by blast
  fix x show "(match ys zs \<circ> match xs ys) x = match xs zs x"
    
  proof (cases "x \<in> set xs")
    case True note x = True
    hence "match xs ys x \<in> set ys"  
      by (simp add: l(1) match_set s) 
    show ?thesis 
      apply(rule match_unique[OF l(1) ss _ x])
      unfolding map_comp_map[symmetric] unfolding o_def
      apply(subst map_match[OF l(1) s(1)])
      apply(subst map_match[OF l(2) s(2)])
      ..
  next
    case False
    thus ?thesis unfolding o_def sledgehammer


lemma bij_betw_match: 
assumes 1: "sameShape xs ys" and 2: "linear xs" "linear ys" and 3: "x \<in> set xs"
shows "match xs ys (match ys xs x) = x"
proof-
  have "(match xs ys o match ys xs) x = x"
    apply(rule cong_rev_id[OF _ 3])
    unfolding map_comp_map[symmetric] unfolding o_def
    unfolding find_theorems map name: comp using  match
  

lemma bij_betw_match: 
assumes "sameShape xs ys" "linear xs" "linear ys"
shows "bij_betw (match xs ys) (set xs) (set ys)"
proof-
  {fix x assume x: "x \<in> set xs"
   have ""

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
