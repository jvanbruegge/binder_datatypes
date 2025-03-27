theory PermFreeV_comodel_is_SwapFreshV_comodel
imports SwapFresh_SwapFreshV_comodels PermFree_PermFreeV_comodels 
begin 

context PermFreeV_comodel 
begin

definition swapD :: "'D \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'D" where 
"swapD = toSwp permD" 

lemma swapD_id[simp]: "swapD c x x = c"
by (simp add: swapD_def toSwp_def) 

lemma swapD_idem[simp]: "swapD (swapD c x y) x y = c"
using nswapping_sym0 nswapping_sym1 nswapping_toSwp permutFvars_def2 
using PmId_PmCp swapD_def by fastforce 

lemma SwId_SwIv_SwCp: "nswapping swapD"
by (simp add: PmId_PmCp nswapping_toSwp swapD_def)

lemma swappingSwFv_swapD_FvarsD: "swappingSwFv swapD FvarsD"
by (simp add: PmFv swapD_def swappingSwFv_toSwp)

lemma SwVrI: "\<And> z1 z2 a x. 
  DestD a = Vv x \<Longrightarrow> DestD (swapD a z1 z2) = Vv (sw x z1 z2)"
by (simp add: PmVrI swapD_def toSwp_def)

lemma SwApI: "\<And> z1 z2 a a1 a2. 
  DestD a = Aa (a1,a2) \<Longrightarrow> DestD (swapD a z1 z2) = Aa (swapD a1 z1 z2, swapD a2 z1 z2)"
by (simp add: PmApI swapD_def toSwp_def)

lemma SwLmI: "DestD aa = Ll K \<Longrightarrow> 
  \<exists>K'. DestD (swapD aa z1 z2) = Ll K' \<and>  
  (\<forall>x a. (x,a) \<in> K \<longrightarrow> (sw x z1 z2, swapD a z1 z2) \<in> K')"
apply (simp add: PmLmI swapD_def toSwp_def)
using PmLmI[of "id(z1 := z2, z2 := z1)" aa K]  
using sw_def by fastforce

lemma permD_swapD: "swapD d z1 z2 = permD d (id(z1 := z2, z2 := z1))"
by (simp add: swapD_def toSwp_def)

(* *)
definition freshD :: "var \<Rightarrow> 'D \<Rightarrow> bool" where 
  "freshD x d \<equiv> x \<notin> FvarsD d"

lemma FrVrI: "\<And> z a x. freshD z a \<Longrightarrow> DestD a = Vv x \<Longrightarrow> z \<noteq> x"
and  
FrApI: "\<And> z a a1 a2. 
  freshD z a \<Longrightarrow> DestD a = Aa (a1,a2)
  \<Longrightarrow> freshD z a1 \<and> freshD z a2"
and  
FrLmI: "\<And> z aa K x a. 
  freshD z aa \<Longrightarrow> DestD aa = Ll K \<Longrightarrow> (x,a) \<in> K \<Longrightarrow> (z = x \<or> freshD z a)"
using FvVrI FvApI FvLmI unfolding freshD_def by blast+

lemma SwFr: "swappingSwFr swapD freshD"
by (smt (verit, best) freshD_def swappingSwFr_def swappingSwFv_def swappingSwFv_swapD_FvarsD)

end (* context PermFreeV_comodel  *)


lemma PermFreeV_comodel_implies_SwapFreshV_comodel: 
assumes m: "PermFreeV_comodel DestD permD FvarsD" 
shows "SwapFreshV_comodel DestD (PermFreeV_comodel.swapD permD) (PermFreeV_comodel.freshD FvarsD)"
using PermFreeV_comodel.DestD_LmD_NE[OF m] 
PermFreeV_comodel.FrVrI[OF m]  PermFreeV_comodel.FrApI[OF m] 
PermFreeV_comodel.FrLmI[OF m]  
PermFreeV_comodel.SwVrI[OF m]  
PermFreeV_comodel.SwApI[OF m] 
PermFreeV_comodel.SwLmI[OF m]  
PermFreeV_comodel.SwId_SwIv_SwCp[OF m]  
PermFreeV_comodel.SwFr[OF m]  
PermFreeV_comodel.PmBvrI[OF m]  PermFreeV_comodel.freshD_def[OF m] 
PermFreeV_comodel.permD_swapD[OF m]  
PermFreeV_comodel.swapD_id[OF m]
unfolding SwapFreshV_comodel_def SwapFreshV_comodel_axioms_def
SwapFresh_Basic_comodel_def apply safe by metis+

sublocale PermFreeV_comodel < SwapFreshV_comodel 
where swapD = swapD and freshD = freshD apply standard 
  subgoal using DestD_LmD_NE .
  subgoal using FrVrI . 
  subgoal using FrApI . 
  subgoal using FrLmI . 
  subgoal using SwVrI .
  subgoal using SwApI .
  subgoal using SwLmI .
  subgoal using SwId_SwIv_SwCp .
  subgoal using SwFr .
  subgoal by (metis PmBvrI freshD_def permD_swapD swapD_id) .


end 