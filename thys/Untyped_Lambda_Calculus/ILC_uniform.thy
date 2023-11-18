(* Here we instantiate the general enhanced rule induction to the "reneqv" predicate from Mazza  *)
theory ILC_uniform
imports ILC_Renaming_Equivalence
begin

(* We already know equivariance from the general infrastructure: *)
lemma rrename_reneqv:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" and r: "reneqv e e'" 
shows "reneqv (rrename f e) (rrename f e')"
using assms unfolding reneqv_I using Reneqv.I_equiv[of "(e,e')" f]
unfolding Tmap_def ssbij_def by auto


lemma reneweqv_sym:
"reneqv e e' \<Longrightarrow> reneqv e' e"
apply(induct rule: reneqv.induct) 
apply (auto intro: reneqv.intros)  
by (metis Un_iff iApp insert_subset)


lemma reneqv_iVar_casesL:
"reneqv (iVar x) e' \<Longrightarrow> 
 (\<exists> xs x'. e' = iVar x' \<and> ssuper xs \<and> {x,x'} \<subseteq> dsset xs)"
apply(erule reneqv.cases) by auto

lemma reneqv_iVar_casesR:
"reneqv e (iVar x') \<Longrightarrow> 
 (\<exists> xs x. e = iVar x \<and> ssuper xs \<and> {x,x'} \<subseteq> dsset xs)"
apply(erule reneqv.cases) by auto


thm iLam_inject


lemma reneqv_Fvars: "reneqv e e' \<Longrightarrow> 
{xs . ssuper xs \<and> FFVars e \<inter> dsset xs \<noteq> {}} = {xs . ssuper xs \<and> FFVars e' \<inter> dsset xs \<noteq> {}}" 
apply(induct rule: reneqv.induct) 
apply auto sorry


find_theorems inv_into

thm iLam_inject[no_vars]

lemma iLam_inject_avoid: 
assumes "|X::ivar set| <o |UNIV::ivar set|" "X \<inter> dsset xs = {}" "X \<inter> dsset xs' = {}"
shows 
"(iLam xs e = iLam xs' e') = 
 (\<exists>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and> id_on (FFVars (iLam xs e)) f \<and> id_on X f \<and> 
      dsmap f xs = xs' \<and> rrename f e = e')"
sorry

lemma iLam_eq_super: 
assumes "iLam xs e = iLam xsa ea"
shows "ssuper xs \<longleftrightarrow> ssuper xsa"
using assms assms[THEN sym]
unfolding iLam_inject  
by (metis rrename_ssuper)

lemma reneqv_iLam_casesL:
assumes "reneqv (iLam xs e) ee'"
shows "\<exists> e'. ee' = iLam xs e' \<and> ssuper xs \<and> reneqv e e'"
proof-
  obtain xsa ea ea' where il: "iLam xs e = iLam xsa ea" and ee': "ee' = iLam xsa ea'" 
  and ss: "ssuper xsa" and r: "reneqv ea ea'" 
  using assms by cases auto
  have 0: "|FFVars ee'| <o |UNIV::ivar set|"  
    by (simp add: iterm.set_bd_UNIV)
  have "reneqv (iLam xsa ea) ee'"  
    using assms il by force
  moreover have "FFVars (iLam xsa ea) \<inter> dsset xs = {}"  
    by (metis DiffD2 disjointI il iterm.set(3))
  moreover have "ssuper xs" using iLam_eq_super il ss by blast
  ultimately have 1: "FFVars ee' \<inter> dsset xs = {}"  
    using reneqv_Fvars by fastforce
  have 2: "FFVars ee' \<inter> dsset xsa = {}"  
    unfolding ee' by auto
  
  obtain f where f: " bij f" "|supp f| <o |UNIV::ivar set|" "id_on (FFVars (iLam xs e)) f"
  and ff: "id_on (FFVars ee') f" 
  and xsa: "xsa = dsmap f xs" and ea: "ea = rrename f e"
  using il[unfolded iLam_inject_avoid[OF 0 1 2]] by auto
  hence e: "e = rrename (inv f) ea" by (metis inv_simp1 iterm.rrename_bijs iterm.rrename_inv_simps)

  show ?thesis apply(rule exI[of _ "rrename (inv f) ea'"]) apply(intro conjI)
    subgoal unfolding ee' xsa unfolding iLam_inject apply(rule exI[of _ "inv f"])
    using f ff unfolding id_on_def ee'  
    apply (auto simp add: dstream.map_comp)  
    by (metis bij_imp_inv dstream.set_map xsa) 
    subgoal by fact
    subgoal unfolding e apply(rule rrename_reneqv) using f r by auto .
qed
  


lemma reneqv_trans:
"reneqv e e' \<Longrightarrow> reneqv e' e'' \<Longrightarrow> reneqv e e''"
proof(induct arbitrary: e'' rule: reneqv.induct)
  case (iVar xs x x')
  then show ?case using reneqv_iVar_casesL[OF iVar(3)]
  using super_disj by (auto intro!: reneqv.iVar) 
next
  case (iLam xs e e')
  then show ?case sorry
next
  case (iApp e1 e1' es2 es2')
  then show ?case sorry
qed 


end