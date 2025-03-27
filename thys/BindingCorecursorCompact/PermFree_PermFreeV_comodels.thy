theory PermFree_PermFreeV_comodels 
  imports Swap_vs_Perm
begin 


(* Nominal-logic permutation-style freshness, the countability-based version: *)
definition npfresh:: "('c \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> 'c) \<Rightarrow> var \<Rightarrow> 'c \<Rightarrow> bool" where
  "npfresh prm x c \<equiv> countable {y . prm c (id(x:=y,y:=x)) \<noteq> c}"

locale PermFree_comodel =   
fixes DestD :: "'D \<Rightarrow> var + 'D \<times> 'D + (var \<times> 'D) set"
(* *)
and permD :: "'D \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> 'D"
and FvarsD :: "'D \<Rightarrow> var set"
assumes 
DestD_LmD_NE: "\<And>d K. DestD d = Ll K \<Longrightarrow> K \<noteq> {}" 
and 
PmId_PmCp: "permut permD"
(* the countable-support assumption is not needed *)
and
PmVrI: "\<And> pi a x. fsupp pi \<Longrightarrow> bij pi \<Longrightarrow> 
  DestD a = Vv x \<Longrightarrow> DestD (permD a pi) = Vv (pi x)"
and 
PmApI: "\<And> pi a a1 a2. fsupp pi \<Longrightarrow> bij pi \<Longrightarrow>
  DestD a = Aa (a1,a2) \<Longrightarrow> DestD (permD a pi) = Aa (permD a1 pi, permD a2 pi)"
and 
PmLmI: "\<And> pi aa K . fsupp pi \<Longrightarrow> bij pi \<Longrightarrow>
  DestD aa = Ll K \<Longrightarrow> 
  \<exists>K'. DestD (permD aa pi) = Ll K' \<and>  
  (\<forall>x a. (x,a) \<in> K \<longrightarrow> (pi x, permD a pi) \<in> K')"
and 
(* *)
FvDPmI: "\<And>d. FvarsD d = {x . \<not> countable {y . permD d (id(x:=y,y:=x)) \<noteq> d}}"
(* We don't need FCB or any destructor-based vriation of it, such as: 
FCBI: "\<exists> z. \<forall> dd K d. DestD dd = Ll K \<and> (z,d) \<in> K \<longrightarrow> z \<notin> FvarsD dd"
*)
(* but this one must be added: *)
and PmBvrI: 
"\<And>dd K x d x' d'. DestD dd = Ll K \<Longrightarrow> {(x,d),(x',d')} \<subseteq> K \<Longrightarrow> 
 (x' = x \<or> npfresh permD x' d) \<and> permD d (id(x:=x',x':=x)) = d'"
begin

lemma SwCgI: "\<And> dd K x d x' d'. DestD dd = Ll K \<Longrightarrow> {(x,d),(x',d')} \<subseteq> K \<Longrightarrow> 
 \<exists>z. (z = x \<or> npfresh permD z d) \<and> (z = x' \<or> npfresh permD z d') \<and> 
 permD d (id(x:=z,z:=x)) = permD d' (id(x':=z,z:=x'))"
by (metis PmBvrI insert_subset)

lemma npfresh_iff_FvarsD: "npfresh permD x d \<longleftrightarrow> x \<notin> FvarsD d"
unfolding npfresh_def FvDPmI by fastforce  

lemma FvarsD_npfresh: "FvarsD d = {x. \<not> npfresh permD x d}"
unfolding npfresh_iff_FvarsD by auto

lemma permD_id[simp]: "permD d id = d"  
	by (meson permut_def PmId_PmCp)  

lemma permD_id'[simp]: "permD d (\<lambda>x. x) = d"
by (metis comp_id fun.map_ident permD_id)

lemma permD_comp: "fsupp pi \<Longrightarrow> bij pi \<Longrightarrow> fsupp pi' \<Longrightarrow> bij pi' \<Longrightarrow> 
permD d (pi o pi') = permD (permD d pi') pi"
by (metis permut_def PmId_PmCp)

end (* context PermFree_comodel *)

locale PermFreeV_comodel =   
fixes DestD :: "'D \<Rightarrow> var + 'D \<times> 'D + (var \<times> 'D) set"
(* *)
and permD :: "'D \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> 'D"
and FvarsD :: "'D \<Rightarrow> var set"
assumes 
DestD_LmD_NE: "\<And>d K. DestD d = Ll K \<Longrightarrow> K \<noteq> {}" 
and  
PmId_PmCp: "permut permD"
and  
PmFv: "permutPmFv permD FvarsD"
and 
(* *)
FvVrI: "\<And> a x. DestD a = Vv x \<Longrightarrow> x \<in> FvarsD a"
and  
FvApI: "\<And> a a1 a2. 
  DestD a = Aa (a1,a2)
  \<Longrightarrow> FvarsD a1 \<union> FvarsD a2 \<subseteq> FvarsD a"
and  
FvLmI: "\<And> aa K x a. 
  DestD aa = Ll K \<Longrightarrow> (x,a) \<in> K \<Longrightarrow> 
  FvarsD a - {x} \<subseteq> FvarsD aa"
and
(* *)
PmVrI: "\<And> pi a x. fsupp pi \<Longrightarrow> bij pi \<Longrightarrow> 
  DestD a = Vv x \<Longrightarrow> DestD (permD a pi) = Vv (pi x)"
and 
PmApI: "\<And> pi a a1 a2. fsupp pi \<Longrightarrow> bij pi \<Longrightarrow>
  DestD a = Aa (a1,a2) \<Longrightarrow> DestD (permD a pi) = Aa (permD a1 pi, permD a2 pi)"
and 
PmLmI: "\<And> pi aa K . fsupp pi \<Longrightarrow> bij pi \<Longrightarrow>
  DestD aa = Ll K \<Longrightarrow> 
  \<exists>K'. DestD (permD aa pi) = Ll K' \<and>  
  (\<forall>x a. (x,a) \<in> K \<longrightarrow> (pi x, permD a pi) \<in> K')"
and 
PmBvrI: 
"\<And>dd K x d x' d'. DestD dd = Ll K \<Longrightarrow> {(x,d),(x',d')} \<subseteq> K \<Longrightarrow> 
 (x' = x \<or> x' \<notin> FvarsD d) \<and> permD d (id(x':=x,x:=x')) = d'"
begin

lemma PmBvrI': 
"\<And>dd K x d x' d'. DestD dd = Ll K \<Longrightarrow> {(x,d),(x',d')} \<subseteq> K \<Longrightarrow> 
 (x' = x \<or> (x' \<notin> FvarsD d \<and> x \<notin> FvarsD d')) \<and>  permD d (id(x':=x,x:=x')) = d'"
by (smt (z3) PmBvrI insert_commute)


lemma permD_id[simp]: "permD d id = d"
using PmId_PmCp unfolding permut_def by auto

lemma permD_id'[simp]: "permD d (\<lambda>x. x) = d"
by (metis comp_id fun.map_ident permD_id)

lemma permD_comp: "fsupp pi \<Longrightarrow> bij pi \<Longrightarrow> fsupp pi' \<Longrightarrow> bij pi' \<Longrightarrow> 
permD d (pi o pi') = permD (permD d pi') pi"
using PmId_PmCp unfolding permut_def by auto

end (* context PermFreeV_comodel *)



end