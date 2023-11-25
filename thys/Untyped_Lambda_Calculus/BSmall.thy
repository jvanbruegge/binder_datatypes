(* Bound smallness (reusable for at least two relations... *)

theory BSmall 
imports Supervariables
begin

type_synonym B = "ivar dstream option"

fun Bmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> B \<Rightarrow> B" where 
"Bmap f xxs = (case xxs of None \<Rightarrow> None
                          |Some xs \<Rightarrow> Some (dsmap f xs))"

fun Bvars :: "B \<Rightarrow> ivar set" where 
"Bvars xxs = (case xxs of None \<Rightarrow> {}
                         |Some xs \<Rightarrow> dsset xs)"

fun wfB :: "B \<Rightarrow> bool" where 
"wfB xxs = (case xxs of None \<Rightarrow> True
                       |Some xs \<Rightarrow> super xs)"

definition bsmall :: "ivar set \<Rightarrow> bool" where 
"bsmall X \<equiv> finite (touchedSuper X)"

lemma super_dsset_singl: 
 "super ys \<Longrightarrow> {xs . super xs \<and> dsset ys \<inter> dsset xs \<noteq> {}} = {ys}"
apply safe 
apply (meson Int_emptyD super_disj)
by (simp add: dsset_range)

lemma super_Un_ddset_triv: "{xs. super xs \<and> (A \<union> B) \<inter> dsset xs \<noteq> {}} \<subseteq>  
   {xs. super xs \<and> A \<inter> dsset xs \<noteq> {}} \<union> 
   {xs. super xs \<and> B \<inter> dsset xs \<noteq> {}}"
by auto

end 