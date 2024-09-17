theory More_List
imports "../Prelim/Prelim"  "../Prelim/Card_Prelim" 
begin 

(* More on lists: *)

lemmas distinct_def2 = distinct_conv_nth

lemma set_natLeq: "|set vs| <o natLeq"
using finite_iff_ordLess_natLeq by blast 

definition theN where 
"theN vs v \<equiv> SOME i. i < length vs \<and> nth vs i = v"

lemma theN: "v \<in> set vs \<Longrightarrow> theN vs v < length vs \<and> nth vs (theN vs v) = v"
unfolding theN_def apply(rule someI_ex) by (meson in_set_conv_nth)

lemma theN_inj1: "distinct vs \<Longrightarrow> v \<in> set vs \<Longrightarrow> i < length vs \<Longrightarrow> 
  nth vs i = nth vs (theN vs v) \<Longrightarrow> i = theN vs v"
using theN[of v vs] unfolding distinct_def2 by fastforce

lemma theN_inj: "distinct vs \<Longrightarrow> v1 \<in> set vs \<Longrightarrow> v2 \<in> set vs \<Longrightarrow>
  nth vs (theN vs v1) = nth vs (theN vs v2) \<Longrightarrow> v1 = v2"
using theN_inj1 by (simp add: theN)

lemma inj_on_theN: "distinct vs \<Longrightarrow> inj_on (theN vs) (set vs)"
unfolding inj_on_def by (auto simp add: theN_inj)

lemma surj_theN: "distinct vs \<Longrightarrow> theN vs ` (set vs) = {..<length vs}"
unfolding image_def apply auto
  apply (simp add: theN)
  by (metis nth_mem theN theN_inj1)

lemma bij_betw_theN: "distinct vs \<Longrightarrow> bij_betw (theN vs) (set vs) {..<length vs}"
unfolding bij_betw_def using inj_on_theN surj_theN by auto

lemma theN_nth[simp]: "distinct vs \<Longrightarrow> i < length vs \<Longrightarrow> theN vs (nth vs i) = i"
by (meson nth_eq_iff_index_eq nth_mem theN)

lemma inj_on_distinct_smap: 
"inj_on f (set xs) \<Longrightarrow> distinct xs \<Longrightarrow> distinct (map f xs)"
using distinct_map by blast 

lemma distinct_smap: 
"distinct (map f xs) \<Longrightarrow> distinct xs" 
unfolding distinct_def2 by auto metis

lemma inj_on_distinct_smap'[simp]: 
"inj_on f (set xs) \<Longrightarrow> distinct (map f xs) \<longleftrightarrow> distinct xs"
by (meson inj_on_distinct_smap distinct_smap)

lemma bij_distinct_smap: 
"bij f \<Longrightarrow> distinct xs \<Longrightarrow> distinct (map f xs)"
by (simp add: inj_on_def inj_on_distinct_smap)

lemma bij_distinct_smap'[simp]: 
"bij f \<Longrightarrow> distinct (map f xs) \<longleftrightarrow> distinct xs"
by (simp add: inj_on_def inj_on_distinct_smap)

end