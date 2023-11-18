(* Here we instantiate the general enhanced rule induction to the "reneqv" predicate from Mazza  *)
theory ILC_uniform
imports ILC_Renaming_Equivalence
begin

(*
lemma rrename_reneqv:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" and r: "reneqv e e'" 
shows "reneqv (rrename f e) (rrename f e')"
using r proof(induct rule: reneqv.induct)
  case (iVar xs x x')
  show ?case using f apply simp 
  apply(rule reneqv.iVar[of "dsmap f xs" "f x" "f x'"]) 
next
  case (iLam xs e e')
  then show ?case sorry
next
  case (iApp e1 e1' es2 es2')
  then show ?case sorry
qed 
*)



lemma reneweqv_sym:
"reneqv e e' \<Longrightarrow> reneqv e' e"
apply(induct rule: reneqv.induct) 
apply (auto intro: reneqv.intros)  
by (metis Un_iff iApp insert_subset)


lemma reneqv_iVar_casesL:
"reneqv (iVar x) e' \<Longrightarrow> 
 (\<exists> xs x'. e' = iVar x' \<and> super xs \<and> {x,x'} \<subseteq> dsset xs)"
apply(erule reneqv.cases) by auto

lemma reneqv_iVar_casesR:
"reneqv e (iVar x') \<Longrightarrow> 
 (\<exists> xs x. e = iVar x \<and> super xs \<and> {x,x'} \<subseteq> dsset xs)"
apply(erule reneqv.cases) by auto

lemma reneqv_iLam_casesL:
"reneqv (iLam xs e) ee' \<Longrightarrow> 
 (\<exists> e'. ee' = iLam xs e' \<and> super xs)"
apply(erule reneqv.cases) by auto


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