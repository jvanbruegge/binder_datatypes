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


(* *)

definition "sameShape (xs::('a::var) list) (ys::'a list) \<equiv> list_all2 (\<lambda>_ _. True) xs ys"

(* can also have generic proofs: *)
lemma sameShape_refl: "sameShape xs xs" 
  by (simp add: list.rel_refl sameShape_def)
lemma sameShape_sym: "sameShape xs ys \<Longrightarrow> sameShape ys xs" 
  by (simp add: list_all2_conv_all_nth sameShape_def)
lemma sameShape_trans: "sameShape xs ys \<Longrightarrow> sameShape ys zs \<Longrightarrow> sameShape xs zs" 
by (simp add: list_all2_conv_all_nth sameShape_def)
lemma sameShape_map1: "sameShape (map f xs) xs"
by (simp add: list_all2_conv_all_nth sameShape_def)
lemma sameShape_map2: "sameShape xs (map f xs)"
by (simp add: list_all2_conv_all_nth sameShape_def)

hide_const linear
definition "linear (xs::('a :: var) list) \<equiv> \<forall>ys. sameShape xs ys \<longrightarrow> (\<exists>f. map f xs = ys)"

lemma linear_imp: 
assumes "linear xs" "sameShape xs ys" 
shows "\<exists>f. map f xs = ys \<and> supp f \<subseteq> set xs"
proof-
  obtain f where ys: "map f xs = ys" using assms unfolding linear_def by auto
  define g where "g \<equiv> \<lambda>x. if x \<in> set xs then f x else x"
  show ?thesis
  apply(rule exI[of _ g], safe)
    subgoal unfolding ys[symmetric] apply(rule map_cong)
      subgoal ..
      subgoal unfolding g_def by auto .
    subgoal unfolding g_def supp_def by (auto split: if_splits) .
qed
    
  
  

(* generic for rigid BNFs: *)
abbreviation "any \<equiv> undefined"
definition "rigid (dummy::'a) \<equiv> \<forall>(f::'a\<Rightarrow>'a) (g::'a\<Rightarrow>'a) (xs::('a :: var) list) (x::'a). map f xs = map g xs \<and> x \<in> set xs \<longrightarrow> f x = g x"
(* lists are rigid, but I will not use this, to emphasize where rigidity is needed: *)
lemma cong_rev: "map f xs = map g xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x = g x"
  (* by fastforce *) oops

lemma cong_rev: "rigid (any::'a::var) \<Longrightarrow> map f xs = map g xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x = g x"
unfolding rigid_def by fastforce


lemma cong_rev_id: "rigid (any::'a::var) \<Longrightarrow> map f (xs::'a list) = xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x = x"
  using cong_rev[of f xs id] by auto

definition "match (xs::('a :: var) list) ys \<equiv> SOME f. map f xs = ys \<and> (supp f \<subseteq> set xs)"

lemma match:
"linear xs \<Longrightarrow> sameShape xs ys \<Longrightarrow> map (match xs ys) xs = ys \<and> supp (match xs ys) \<subseteq> set xs"  
using someI[of "\<lambda>f. map f xs = ys \<and> supp f \<subseteq> set xs"] 
using linear_imp unfolding match_def by blast

lemmas map_match = match[THEN conjunct1]
lemmas supp_match = match[THEN conjunct2]

lemma finite_supp_match:
"linear xs \<Longrightarrow> sameShape xs ys \<Longrightarrow> finite (supp (match xs ys))"  
by (metis List.finite_set match rev_finite_subset) 

lemma card_supp_match:
"linear (xs::('a :: var) list) \<Longrightarrow> sameShape xs ys \<Longrightarrow> 
 |supp (match xs ys)| <o |UNIV::'a set|"  
by (simp add: finite_supp_match infinite_UNIV)

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
by (simp add: assms(1,2) image_set map_match)

lemma match_set: 
assumes "sameShape xs ys" "linear xs" "x \<in> set xs"
shows "match xs ys x \<in> set ys"
  using assms image_match_set by auto

lemma match_id: 
assumes "rigid (any::'a::var)" "linear (xs::'a list)" "x \<in> set xs"
shows "match xs xs x = x"
by (meson assms cong_rev_id map_match sameShape_refl)

lemma match_trans: 
assumes l: "linear xs" "linear ys" and s: "sameShape xs ys" "sameShape ys zs" 
and xs: "x \<in> set xs"
shows "match ys zs (match xs ys x) = match xs zs x"
proof-
  have ss: "sameShape xs zs"  
  using s(1,2) sameShape_trans by blast
  have ys: "match xs ys x \<in> set ys"  
  by (simp add: l(1) match_set s xs) 
  have "(match ys zs o match xs ys) x = match xs zs x"
  apply(rule match_unique[OF l(1) ss _ xs])
  unfolding map_comp_map[symmetric] unfolding o_def
  apply(subst map_match[OF l(1) s(1)])
  apply(subst map_match[OF l(2) s(2)])
  ..
  thus ?thesis by simp
qed 

lemma match_rev: 
assumes r: "rigid (any::'a::var)" and 
l: "linear (xs::'a list)" "linear ys" and s: "sameShape xs ys" and x: "x \<in> set xs"
shows "match ys xs (match xs ys x) = x"
  apply(subst match_trans[OF l s sameShape_sym[OF s] x])
  apply(rule match_id[OF r l(1) x]) .   

lemma bij_betw_match: 
assumes "rigid (any::'a::var)" "sameShape (xs::'a list) ys" "linear xs" "linear ys"
shows "bij_betw (match xs ys) (set xs) (set ys)"
by (smt (verit, best) assms bij_betwI' match_rev match_set sameShape_sym)

lemma inj_on_linear: 
assumes l: "linear (xs::('a::var) list)" and i: "inj_on f (set xs)"
shows "linear (map (f::'a\<Rightarrow>'a) xs)"
unfolding linear_def proof safe
  fix ys assume "sameShape (map f xs) ys"
  hence ss: "sameShape xs ys" 
    using sameShape_map2 sameShape_trans by blast
  then obtain h where m: "map h xs = ys" using l unfolding linear_def by auto
  show "\<exists>g. map g (map f xs) = ys"
  apply(rule exI[of _ "h o inv_into (set xs) f"])
  apply simp unfolding m[symmetric] apply(rule map_cong)
  using i by auto
qed

lemma bij_linear: 
assumes 1: "linear (xs::('a::var) list)" and 2: "bij f"
shows "linear (map (f::'a\<Rightarrow>'a) xs)"
apply(rule inj_on_linear[OF 1])
using assms by (metis bij_not_equal_iff inj_onCI) 



(* *)
definition swap :: "('a::var) list \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a)" where
"swap xs ys x \<equiv> 
 if x \<in> set xs then match xs ys x 
 else if x \<in> set ys then match ys xs x 
 else x"

lemma supp_swap: "supp (swap xs ys) \<subseteq> set xs \<union> set ys"
  unfolding supp_def swap_def by auto

lemma finite_supp_swap: "finite (supp (swap xs ys))"
by (meson List.finite_set finite_UnI finite_subset supp_swap)

lemma card_supp_swap: "|supp (swap (xs::('a::var) list) ys)| <o |UNIV::'a set|"
by (simp add: finite_supp_swap infinite_UNIV)

lemma imsupp_swap: "linear xs \<Longrightarrow> linear ys \<Longrightarrow> sameShape xs ys \<Longrightarrow> imsupp (swap xs ys) \<subseteq> set xs \<union> set ys"
unfolding imsupp_def supp_def swap_def 
using match_set sameShape_sym by auto blast+

lemma swap_sym: "set xs \<inter> set ys = {} \<Longrightarrow> swap xs ys = swap ys xs"
  unfolding supp_def swap_def fun_eq_iff by auto

lemma swap_idem: 
assumes "rigid (any::'a::var)" "linear (xs::'a list)" "linear ys" "sameShape xs ys" "set xs \<inter> set ys = {}"
shows "swap xs ys o swap xs ys = id"
apply(rule ext)
using assms unfolding swap_def 
by simp (meson Int_emptyD match_rev match_set sameShape_sym)

lemma bij_swap: "rigid (any::'a::var) \<Longrightarrow> linear (xs::'a list) \<Longrightarrow> linear ys \<Longrightarrow> sameShape xs ys \<Longrightarrow> set xs \<inter> set ys = {} \<Longrightarrow> 
bij (swap xs ys)"
  using o_bij swap_idem by blast

lemma map_swap1: "linear xs \<Longrightarrow> linear ys \<Longrightarrow> sameShape xs ys \<Longrightarrow> set xs \<inter> set ys = {} \<Longrightarrow> 
map (swap xs ys) xs = ys"
  by (metis map_eq_conv map_match swap_def)

lemma map_swap2: "linear xs \<Longrightarrow> linear ys \<Longrightarrow> sameShape xs ys \<Longrightarrow> set xs \<inter> set ys = {} \<Longrightarrow> 
map (swap xs ys) ys = xs"
by (metis inf.commute map_swap1 sameShape_sym swap_sym)



(****)

(* Current: *)
lemma Lam_Inj: "Lam xs t = Lam xs' t' \<longleftrightarrow> (\<exists>f. bij (f::'a::var \<Rightarrow> 'a) \<and>
  |supp f| <o |UNIV::'a set| \<and> map f xs = xs' \<and> 
  (\<forall>x\<in> FVars_term t - set xs. f x = x) \<and> permute_term f t = t')"
  sorry

(* Symmetric variant (with existential ys): *)
lemma Lam_Inj_sym: "Lam (xs::'a::var list) t = Lam xs' t' \<longleftrightarrow> 
(\<exists>ys f f'.
  set ys \<inter> (set xs \<union> set xs' \<union> FVars_term t \<union> FVars_term t') = {} \<and>
  bij f \<and> |supp f| <o |UNIV::'a set| \<and> supp f \<subseteq> set xs \<union> set ys \<and> map f xs = ys \<and> 
     (\<forall>x\<in> FVars_term t - set xs. f x = x) \<and> 
  bij f' \<and> |supp f'| <o |UNIV::'a set| \<and> supp f' \<subseteq> set xs' \<union> set ys \<and> map f' xs' = ys \<and> 
     (\<forall>x\<in> FVars_term t' - set xs'. f' x = x) \<and> 
  permute_term f t = permute_term f' t')"
  sorry
(* TODO: revive/adapt Jan's proof *)

(* Getting rid of f and f' with the help of linearity (we can only do this 
from the symmetric version! because we need disjointness in order to swap)*)
lemma Lam_Inj_sym_linear: 
assumes "rigid (any::'a::var)" "linear (xs::'a::var list)" "linear xs'"
shows "Lam xs t = Lam xs' t' \<longleftrightarrow> 
(\<exists>ys.
  set ys \<inter> (set xs \<union> set xs' \<union> FVars_term t \<union> FVars_term t') = {} \<and> 
  linear ys \<and> sameShape ys xs \<and> sameShape ys xs' \<and>  
  permute_term (swap xs ys) t = permute_term (swap xs' ys) t')"
proof safe
  fix ys assume 0: "set ys \<inter> (set xs \<union> set xs' \<union> FVars_term t \<union> FVars_term t') = {}"
  "linear ys" "sameShape ys xs" "sameShape ys xs'"
  "permute_term (swap xs ys) t = permute_term (swap xs' ys) t'"
  hence ss: "set ys \<inter> set xs = {}" "set ys \<inter> set xs' = {}" by auto
  show "Lam xs t = Lam xs' t'"
  unfolding Lam_Inj_sym apply(rule exI[of _ ys]) 
  apply(rule exI[of _ "swap xs ys"]) apply(rule exI[of _ "swap xs' ys"])
  using 0 ss assms apply (intro conjI)
    subgoal by assumption  
    subgoal using bij_swap swap_sym by metis
    subgoal using card_supp_swap .
    subgoal using supp_swap .
    subgoal using map_swap2 swap_sym by metis
    subgoal by (metis Diff_iff IntE Int_emptyD Un_Int_eq(2,3) swap_def swap_sym ) 
    subgoal using bij_swap swap_sym by metis
    subgoal using card_supp_swap .
    subgoal using supp_swap by metis
    subgoal using map_swap2 swap_sym by metis
    subgoal by (metis Diff_iff Int_emptyD UnCI swap_def)
    subgoal by assumption .
next
  assume "Lam xs t = Lam xs' t'" 
  then obtain ys f f' where 
  ss: "set ys \<inter> (set xs \<union> set xs' \<union> FVars_term t \<union> FVars_term t') = {}" and 
  f: "bij f" "|supp f| <o |UNIV::'a set|" "supp f \<subseteq> set xs \<union> set ys" "map f xs = ys" 
    "\<forall>x\<in>FVars_term t - set xs. f x = x" and 
  f': "bij f'" "|supp f'| <o |UNIV::'a set|" "supp f' \<subseteq> set xs' \<union> set ys \<and> map f' xs' = ys"  
    "\<forall>x\<in>FVars_term t' - set xs'. f' x = x" and
  p: "permute_term f t = permute_term f' t'" unfolding Lam_Inj_sym by blast

  have p1: "permute_term (swap xs ys) t = permute_term f t" 
  apply(rule term.permute_cong) 
    subgoal by (metis Int_Un_emptyI1 bij_swap assms(1,2) bij_linear f(1,4) 
       sameShape_map1 ss swap_sym)
    subgoal using card_supp_swap .
    subgoal by fact
    subgoal by fact
    subgoal by (metis (full_types) Diff_iff Int_Un_empty Int_Un_emptyI1 Int_commute 
     Int_emptyD assms(1,2) bij_linear cong_rev f(1,4,5) map_swap1 sameShape_map2 ss swap_def) .
  have p2: "permute_term (swap xs' ys) t' = permute_term f' t'"
  apply(rule term.permute_cong) 
    subgoal by (metis Int_Un_empty LC.bij_swap Un_commute assms(1,3) bij_linear f'(1,3) 
      sameShape_map1 ss swap_sym)
    subgoal using card_supp_swap .
    subgoal by fact
    subgoal by fact
    subgoal by (metis (full_types) Diff_iff Int_Un_empty Int_Un_emptyI2 Int_commute 
      Int_emptyD assms(1,3) bij_linear cong_rev f'(1,3,4) map_swap1 sameShape_map2 ss swap_def) .
  show "\<exists>ys. set ys \<inter> (set xs \<union> set xs' \<union> FVars_term t \<union> FVars_term t') = {} \<and> 
         linear ys \<and>
         sameShape ys xs \<and>
         sameShape ys xs' \<and> permute_term (swap xs ys) t = permute_term (swap xs' ys) t'"
  apply(rule exI[of _ ys]) using assms ss f f' p p1 p2  
  apply (auto simp add: bij_linear sameShape_map1 sameShape_map2)  
  apply (metis sameShape_map1) .
qed

(* And a version that works for renaming with matching: *)
lemma Lam_Inj_sym_linear_vvsubst: 
assumes "rigid (any::'a::var)" "linear (xs::('a::var) list)" "linear xs'"
shows "Lam xs t = Lam xs' t' \<longleftrightarrow> 
(\<exists>ys.
  set ys \<inter> (set xs \<union> set xs' \<union> FVars_term t \<union> FVars_term t') = {} \<and> 
  linear ys \<and> sameShape ys xs \<and> sameShape ys xs' \<and>  
  vvsubst (match xs ys) t = vvsubst (match xs' ys) t')"
proof-
  {fix t and xs::"'a::var list" and ys assume "set ys \<inter> (set xs \<union> FVars_term t) = {}"
   "linear xs" "linear ys" "sameShape ys xs"
   hence "vvsubst (match xs ys) t = permute_term (swap xs ys) t"
   apply(subst term.vvsubst_permute[symmetric])
     subgoal by (metis assms(1) Int_Un_emptyI1 LC.bij_swap swap_sym)
     subgoal using card_supp_swap .
     subgoal apply(rule term.map_cong)
       subgoal using card_supp_match sameShape_sym by blast
       subgoal using card_supp_swap by blast
       subgoal ..
       subgoal by (metis (no_types, lifting) Int_Un_emptyI2 Int_emptyD in_mono match 
         notin_supp sameShape_sym swap_def) . .
  } note 1 = this
  show ?thesis using assms 1[of _ xs t] 1 [of _ xs' t'] unfolding Lam_Inj_sym_linear[OF assms] 
  apply(intro ex_cong1) by fastforce 
qed

(* Most user-friendly (lightest) versions -- 
do not make sense for lists, but work for linear types: *)
corollary Lam_Inj_sym_linearType: 
assumes rigidType: "rigid (any::'a::var)" and linearType: "\<And>(xs::'a::var list). linear xs"
shows "Lam (xs::'a::var list) t = Lam xs' t' \<longleftrightarrow> 
(\<exists>ys.
  set ys \<inter> (set xs \<union> set xs' \<union> FVars_term t \<union> FVars_term t') = {} \<and> 
  sameShape ys xs \<and> sameShape ys xs' \<and>  
  permute_term (swap xs ys) t = permute_term (swap xs' ys) t')"
  apply(subst Lam_Inj_sym_linear) using assms by auto

corollary Lam_Inj_sym_linearType_vvsubst: 
assumes rigidType: "rigid (any::'a::var)" and linearType: "\<And>(xs::'a::var list). linear xs"
shows "Lam (xs::'a::var list) t = Lam xs' t' \<longleftrightarrow> 
(\<exists>ys.
  set ys \<inter> (set xs \<union> set xs' \<union> FVars_term t \<union> FVars_term t') = {} \<and> 
  sameShape ys xs \<and> sameShape ys xs' \<and>  
  vvsubst (match xs ys) t = vvsubst (match xs' ys) t')"
apply(subst Lam_Inj_sym_linear_vvsubst) using assms by auto

(* The above instantiates nicely to:
-- lambda-terms
-- infinitary lambda-terms
-- POPLmark 2B
*)


(* 
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
*)



end
