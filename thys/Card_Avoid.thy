theory Card_Avoid
imports 
  "Prelim.Prelim"
begin 

definition "suppGr f \<equiv> {(x, f x) | x. f x \<noteq> x}"


lemma supp_incl_suppGr: 
"suppGr f \<subseteq> suppGr g  \<Longrightarrow> supp f \<subseteq> supp g"
unfolding supp_def suppGr_def by auto


lemma extend_id_on': 
assumes g: "bij g" "g o g = id" "id_on A g" 
and A': "A \<subseteq> A'" 
shows "\<exists>f. bij f \<and> suppGr f \<subseteq> suppGr g \<and> id_on A' f"
proof-
  define f where "f \<equiv> 
  \<lambda>a. if a \<in> (A'-A) \<union> g ` (A' - A) then a else g a"
  show ?thesis apply(rule exI[of _ f], intro conjI)
    subgoal using g(1) unfolding bij_def inj_def f_def apply safe
      subgoal by (metis (mono_tags, opaque_lifting) Un_iff comp_def g(2) id_apply image_iff)
      subgoal by auto
      subgoal by (smt (verit) \<open>\<And>y x. \<lbrakk>\<forall>x y. g x = g y \<longrightarrow> x = y; surj g; 
       (if x \<in> A' - A \<union> g ` (A' - A) then x else g x) = (if y \<in> A' - A \<union> g ` (A' - A) then y else g y)\<rbrakk> 
       \<Longrightarrow> x = y\<close> g(2) image_iff pointfree_idE) .
    subgoal unfolding suppGr_def f_def by auto
    subgoal using g(3) unfolding id_on_def f_def by auto .
qed


lemma extend_id_on: 
"bij g \<Longrightarrow> |supp (g::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> \<comment> \<open>|A| <o |UNIV::'a set| \<Longrightarrow> \<close>
 id_on (A - B1) g \<Longrightarrow> B2 \<subseteq> B1 \<Longrightarrow> \<comment> \<open> g ` B1 \<inter> A = {}\<close>  
 \<comment> \<open> added: \<close> g o g = id
 \<Longrightarrow> 
 \<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and> suppGr f \<subseteq> suppGr g \<and> id_on (A - B2) f"
apply(drule extend_id_on'[of g "A - B1" "A-B2"])
  subgoal .  
  subgoal by (meson card_of_diff ordLeq_ordLess_trans) 
  subgoal by auto 
  subgoal apply safe subgoal for f apply(rule exI[of _ f])
  subgoal using supp_incl_suppGr[of f g] by (meson card_of_mono1 ordLeq_ordLess_trans) . . .
  

end