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

lemma super_Un_ddset_triv: "{xs. super xs \<and> (A \<union> B) \<inter> dsset xs \<noteq> {}} \<subseteq>  
   {xs. super xs \<and> A \<inter> dsset xs \<noteq> {}} \<union> 
   {xs. super xs \<and> B \<inter> dsset xs \<noteq> {}}"
by auto

lemma bsmall_emp[simp,intro!]: "bsmall {}" 
unfolding bsmall_def by auto


lemma bsmall_supp_ifd[simp,intro!]: "bsmall (supp id)"
unfolding bsmall_def supp_def by auto

lemma super_bsmall_dsset: "super xs \<Longrightarrow> bsmall (dsset xs)"
by (simp add: bsmall_def)

lemma bsmall_supp_comp: "bsmall (supp g) \<Longrightarrow> bsmall (supp f) \<Longrightarrow> bsmall (supp (g o f))"
unfolding bsmall_def using touchedSuper_supp_comp 
by (metis finite_UnI rev_finite_subset)

lemma bsmall_supp_inv: 
"bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> bsmall (supp f) 
 \<Longrightarrow> bsmall (supp (inv f))"
unfolding bsmall_def by (simp add: touchedSuper_supp_inv)


end 