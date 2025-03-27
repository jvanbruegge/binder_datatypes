theory SwapFresh_SwapFreshV_comodels
  imports Infinitary_Lambda_Terms Swap_vs_Perm
begin 


locale SwapFresh_Basic_comodel = 
fixes 
 DestD :: "'D \<Rightarrow> var + 'D \<times> 'D + (var \<times> 'D) set"
and swapD :: "'D \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'D"
and freshD :: "var \<Rightarrow> 'D \<Rightarrow> bool"
(*  *)
assumes 
DestD_LmD_NE: "\<And>d K. DestD d = Ll K \<Longrightarrow> K \<noteq> {}" 
and 
(* *) 
FrVrI: "\<And> z a x. freshD z a \<Longrightarrow> DestD a = Vv x \<Longrightarrow> z \<noteq> x"
and  
FrApI: "\<And> z a a1 a2. 
  freshD z a \<Longrightarrow> DestD a = Aa (a1,a2)
  \<Longrightarrow> freshD z a1 \<and> freshD z a2"
and  
FrLmI: "\<And> z aa K x a. 
  freshD z aa \<Longrightarrow> DestD aa = Ll K \<Longrightarrow> (x,a) \<in> K \<Longrightarrow> (z = x \<or> freshD z a)"
and 
(* *) 
SwVrI: "\<And> z1 z2 a x. 
  DestD a = Vv x \<Longrightarrow> DestD (swapD a z1 z2) = Vv (sw x z1 z2)"
and 
SwApI: "\<And> z1 z2 a a1 a2. 
  DestD a = Aa (a1,a2) \<Longrightarrow> DestD (swapD a z1 z2) = Aa (swapD a1 z1 z2, swapD a2 z1 z2)"
and 
SwLmI: "\<And> z1 z2 aa K . 
  DestD aa = Ll K \<Longrightarrow> 
  \<exists>K'. DestD (swapD aa z1 z2) = Ll K' \<and>  
  (\<forall>x a. (x,a) \<in> K \<longrightarrow> (sw x z1 z2, swapD a z1 z2) \<in> K')"
begin

definition FvarsD :: "'D \<Rightarrow> var set" where 
  "FvarsD d \<equiv> {x. \<not> freshD x d}"

(* The alternative, freeness-based formulation: *)

lemma FvVrI: "\<And> a x. DestD a = Vv x \<Longrightarrow> x \<in> FvarsD a"
and  
FvApI: "\<And> a a1 a2. 
  DestD a = Aa (a1,a2)
  \<Longrightarrow> FvarsD a1 \<union> FvarsD a2 \<subseteq> FvarsD a"
and  
FvLmI: "\<And> z aa K x a. 
  DestD aa = Ll K \<Longrightarrow> (x,a) \<in> K \<Longrightarrow> 
  FvarsD a - {x} \<subseteq> FvarsD aa"
using FrVrI FrApI FrLmI unfolding FvarsD_def by blast+

end (* context SwapFresh_Basic_comodel *)


locale SwapFreshV_comodel 
=
SwapFresh_Basic_comodel DestD swapD freshD
for DestD :: "'D \<Rightarrow> var + 'D \<times> 'D + (var \<times> 'D) set"
and swapD freshD  
+
assumes (* this needs to be here (unlike in the inductive world) *)
(* nswappingFresh_swapD_freshD: *)
SwId_SwIv_SwCp: "nswapping swapD"
and 
SwFr: "swappingSwFr swapD freshD"
and 
SwBvrI: 
"\<And>dd K x d x' d'. DestD dd = Ll K \<Longrightarrow> {(x,d),(x',d')} \<subseteq> K \<Longrightarrow> 
 (x' = x \<or> freshD x' d) \<and> swapD d x' x = d'"
begin

(* An immediate consequence of RnBvrI: *)
lemma SwCgI:
assumes dd: "DestD dd = Ll K" and xd: "{(x,d),(x',d')} \<subseteq> K"  
shows "\<exists>z. (z = x \<or> freshD z d) \<and> (z = x' \<or> freshD z d') \<and> swapD d z x = swapD d' z x'"
by (metis SwBvrI dd insert_subset xd)


end (* context SwapFreshV_comodel *)


locale SwapFresh_comodel
=
SwapFresh_Basic_comodel DestD swapD freshD 
for DestD :: "'D \<Rightarrow> var + 'D \<times> 'D + (var \<times> 'D) set"
and swapD freshD  
+
assumes  (* again, this needs to be here (unlike in the inductive world) *)
(* nswappingFresh_swapD_freshD *)
SwId_SwIv_SwCp: "nswapping swapD"
and 
SwFr: "swappingSwFr swapD freshD"
and 
FrSw: "swappingFrSw swapD freshD"
and 
SwCgI: "\<And> dd K x d x' d'. DestD dd = Ll K \<Longrightarrow> {(x,d),(x',d')} \<subseteq> K \<Longrightarrow> 
 \<exists>z. (z = x \<or> freshD z d) \<and> (z = x' \<or> freshD z d') \<and> swapD d z x = swapD d' z x'"
begin


lemma RnBvrI: 
assumes d: "DestD dd = Ll K" and xd: "{(x,d),(x',d')} \<subseteq> K" 
shows "(x' = x \<or> freshD x' d) \<and> swapD d x' x = d'"
proof
  obtain z where z: "z = x \<or> freshD z d" "z = x' \<or> freshD z d'"
  "swapD d z x = swapD d' z x'" using SwCgI[OF d xd] by auto
  show 0: "x' = x \<or> freshD x' d" 
  using FrSw (* this is crucially needed to infer renaming from congruence *)
  unfolding swappingFrSw_def  
    by (metis sw_diff sw_eqR z)
  
  show "swapD d x' x = d'" using 0  
  using SwFr SwId_SwIv_SwCp
  unfolding swappingSwFr_def nswapping_def 
  by (smt (verit, ccfv_threshold) sw_diff sw_eqR z(1,3))
qed

end (* context SwapFresh_comodel *)


lemma SwapFresh_comodel_implies_SwapFreshV_comodel: 
assumes "SwapFresh_comodel DestD swapD freshD" 
shows "SwapFreshV_comodel DestD swapD freshD"
unfolding SwapFreshV_comodel_def apply safe
  subgoal using assms unfolding SwapFresh_comodel_def by auto
  subgoal apply unfold_locales  
    subgoal using SwapFresh_comodel.SwId_SwIv_SwCp assms by blast
    subgoal using SwapFresh_comodel.SwFr assms by blast
    subgoal using SwapFresh_comodel.RnBvrI[OF assms] . . . 

sublocale SwapFresh_comodel < SwapFreshV_comodel
by (simp add: SwapFresh_comodel_axioms SwapFresh_comodel_implies_SwapFreshV_comodel)


(**************************************************)
(* Set-based (rather than type-based) version, for better flexibility with corecursion *)

locale SwapFresh_Basic_comodel_setBased = 
fixes D :: "'D set" (* a set cariier D is fixed, and everything is assumed relative to it *)
and DestD :: "'D \<Rightarrow> var + 'D \<times> 'D + (var \<times> 'D) set" 
and swapD :: "'D \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'D"
and freshD :: "var \<Rightarrow> 'D \<Rightarrow> bool"
(*  *)
assumes D_ne: "D \<noteq> {}"
and 
D_closed_DestD_ApD[simp]: 
"\<And>d d1 d2. d \<in> D \<and> DestD d = Aa (d1,d2) \<Longrightarrow> {d1,d2} \<subseteq> D" 
and 
D_closed_DestD_LmD[simp]: "\<And>dd K x d. dd \<in> D \<Longrightarrow> DestD dd = Ll K \<Longrightarrow> (x,d) \<in> K \<Longrightarrow> d \<in> D"
and 
D_closed_swapD[simp]: "\<And>x y d. d \<in> D \<Longrightarrow> swapD d x y \<in> D" 
and 
(* *)
DestD_LmD_NE: "\<And>d K. d \<in> D \<Longrightarrow> DestD d = Ll K \<Longrightarrow> K \<noteq> {}" 
and 
(* *) 
FrVrI: "\<And> z a x. a \<in> D \<Longrightarrow> freshD z a \<Longrightarrow> DestD a = Vv x \<Longrightarrow> z \<noteq> x"
and  
FrApI: "\<And> z a a1 a2. a \<in> D \<Longrightarrow> 
  freshD z a \<Longrightarrow> DestD a = Aa (a1,a2)
  \<Longrightarrow> freshD z a1 \<and> freshD z a2"
and  
FrLmI: "\<And> z aa K x a. aa \<in> D \<Longrightarrow> 
  freshD z aa \<Longrightarrow> DestD aa = Ll K \<Longrightarrow> (x,a) \<in> K \<Longrightarrow> (z = x \<or> freshD z a)"
and 
(* *) 
SwVrI: "\<And> z1 z2 a x. a \<in> D \<Longrightarrow> 
  DestD a = Vv x \<Longrightarrow> DestD (swapD a z1 z2) = Vv (sw x z1 z2)"
and 
SwApI: "\<And> z1 z2 a a1 a2. a \<in> D \<Longrightarrow>
  DestD a = Aa (a1,a2) \<Longrightarrow> DestD (swapD a z1 z2) = Aa (swapD a1 z1 z2, swapD a2 z1 z2)"
and 
SwLmI: "\<And> z1 z2 aa K . 
  DestD aa = Ll K \<Longrightarrow> aa \<in> D \<Longrightarrow>
  \<exists>K'. DestD (swapD aa z1 z2) = Ll K' \<and>  
  (\<forall>x a. (x,a) \<in> K \<longrightarrow> (sw x z1 z2, swapD a z1 z2) \<in> K')"


locale SwapFreshV_comodel_setBased
=
SwapFresh_Basic_comodel_setBased D DestD swapD freshD
for D :: "'D set" and DestD :: "'D \<Rightarrow> var + 'D \<times> 'D + (var \<times> 'D) set"
and swapD freshD  
+
assumes nswappingFresh_swapD_freshD:  
"nswappingOn D swapD \<and> swappingSwFrOn D swapD freshD"
and 
RnBvrI: 
"\<And>dd K x d x' d'. dd \<in> D \<Longrightarrow> 
  DestD dd = Ll K \<Longrightarrow> {(x,d),(x',d')} \<subseteq> K \<Longrightarrow> 
 (x' = x \<or> freshD x' d) \<and> swapD d x' x = d'"
begin

definition "FvarsD d \<equiv> {x. \<not> freshD x d}"

end (* context SwapFreshV_comodel_setBased *)


(**************************************************)
(* Full-corecursion variant: *)

locale SwapFresh_Basic_comodel_setBased_full = 
fixes D :: "'D set"
(* The destructor is now allowed to return an iterm as an option. *)
and DestD :: "'D \<Rightarrow> (var + 'D \<times> 'D + (var \<times> 'D) set) + trm"
and swapD :: "'D \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'D"
and freshD :: "var \<Rightarrow> 'D \<Rightarrow> bool"
(*  *)
assumes 
D_ne: "D \<noteq> {}"
and 
D_closed_DestD_ApD[simp]: 
"\<And>d d1 d2. d \<in> D \<and> DestD d = Inl (Aa (d1,d2)) \<Longrightarrow> {d1,d2} \<subseteq> D" 
and 
D_closed_DestD_LmD[simp]: "\<And>dd K x d. dd \<in> D \<Longrightarrow> DestD dd = Inl (Ll K) \<Longrightarrow> (x,d) \<in> K \<Longrightarrow> d \<in> D"
and 
D_closed_swapD[simp]: "\<And>x y d. d \<in> D \<Longrightarrow> swapD d x y \<in> D" 
and 
(* *)
DestD_LmD_NE: "\<And>d K. d \<in> D \<Longrightarrow> DestD d = Inl (Ll K) \<Longrightarrow> K \<noteq> {}" 
and 
(* *)
FrVrI: "\<And> z a x. a \<in> D \<Longrightarrow> freshD z a \<Longrightarrow> DestD a = Inl (Vv x) \<Longrightarrow> z \<noteq> x"
and  
FrApI: "\<And> z a a1 a2. a \<in> D \<Longrightarrow> 
  freshD z a \<Longrightarrow> DestD a = Inl (Aa (a1,a2))
  \<Longrightarrow> freshD z a1 \<and> freshD z a2"
and  
FrLmI: "\<And> z aa K x a. aa \<in> D \<Longrightarrow> 
  freshD z aa \<Longrightarrow> DestD aa = Inl (Ll K) \<Longrightarrow> (x,a) \<in> K \<Longrightarrow> (z = x \<or> freshD z a)"
and 
freshD_DestD_trm: "\<And> z a t. a \<in> D \<Longrightarrow> 
  freshD z a \<Longrightarrow> DestD a = Inr t
  \<Longrightarrow> fresh z t"
and 
(* *) 
SwVrI: "\<And> z1 z2 a x. a \<in> D \<Longrightarrow> 
  DestD a = Inl (Vv x) \<Longrightarrow> DestD (swapD a z1 z2) = Inl (Vv (sw x z1 z2))"
and 
SwApI: "\<And> z1 z2 a a1 a2. a \<in> D \<Longrightarrow>
  DestD a = Inl (Aa (a1,a2)) \<Longrightarrow> DestD (swapD a z1 z2) = Inl (Aa (swapD a1 z1 z2, swapD a2 z1 z2))"
and 
SwLmI: "\<And> z1 z2 aa K . 
  DestD aa = Inl (Ll K) \<Longrightarrow> aa \<in> D \<Longrightarrow>
  \<exists>K'. DestD (swapD aa z1 z2) = Inl (Ll K') \<and>  
  (\<forall>x a. (x,a) \<in> K \<longrightarrow> (sw x z1 z2, swapD a z1 z2) \<in> K')"
and 
swapD_DestD_trm: "\<And> z1 z2 a t. a \<in> D \<Longrightarrow>
  DestD a = Inr t \<Longrightarrow> DestD (swapD a z1 z2) = Inr (swap t z1 z2)"


locale SwapFreshV_comodel_setBased_full
=
SwapFresh_Basic_comodel_setBased_full D DestD swapD freshD
for D :: "'D set" and DestD :: "'D \<Rightarrow> (var + 'D \<times> 'D + (var \<times> 'D) set) + trm"
and swapD freshD  
+
assumes  
nswappingFresh_swapD_freshD:  
"nswappingOn D swapD \<and> swappingSwFrOn D swapD freshD"
and 
RnBvrI: 
"\<And>dd K x d x' d'. dd \<in> D \<Longrightarrow> 
  DestD dd = Inl (Ll K) \<Longrightarrow> {(x,d),(x',d')} \<subseteq> K \<Longrightarrow> 
 (x' = x \<or> freshD x' d) \<and> swapD d x' x = d'"
begin

(* Starting the reduction of full recursion to iteration: *)

fun DDestD :: "('D + trm) \<Rightarrow> (var + ('D + trm) \<times> ('D + trm) + (var \<times> ('D + trm)) set)" where 
"DDestD (Inl d) = 
 (case DestD d of 
    Inl (Inl x) \<Rightarrow> Vv x
   |Inl (Inr (Inl (d1,d2))) \<Rightarrow> Inr (Inl (Inl d1,Inl d2))
   |Inl (Inr (Inr K)) \<Rightarrow> Inr (Inr {(x, Inl d') | x d' . (x,d') \<in> K})
   |Inr t \<Rightarrow> DDestD (Inr t)
 )"
|
"DDestD (Inr t) = 
 (case Dest t of 
      Inl x \<Rightarrow> Vv x
     |Inr (Inl (t1,t2)) \<Rightarrow> Inr (Inl (Inr t1,Inr t2))
     |Inr (Inr L) \<Rightarrow> Inr (Inr {(x, Inr t) | x t . (x,t) \<in> L}))"

fun sswapD where 
"sswapD (Inl d) z1 z2 = Inl (swapD d z1 z2)"
|
"sswapD (Inr t) z1 z2 = Inr (swap t z1 z2)"

fun ffreshD where 
"ffreshD z (Inl d) = freshD z d"
|
"ffreshD z (Inr t) = fresh z t"

lemma D_closed_DDestD_ApD: 
"dt \<in> D <+> UNIV \<and> DDestD dt = Aa (dt1,dt2) \<Longrightarrow> {dt1,dt2} \<subseteq> D <+> UNIV"
apply(cases dt)
  subgoal for d using D_closed_DestD_ApD[of d] by (auto split: sum.splits)
  subgoal for t by (auto split: sum.splits) .
 
lemma D_closed_DDestD_LmD: 
"ddt \<in> D<+>UNIV \<Longrightarrow> DDestD ddt = Ll K \<Longrightarrow> (x,dt) \<in> K \<Longrightarrow> dt \<in> D <+> UNIV"
apply(cases dt)
  subgoal for d using D_closed_DestD_LmD[of d] by (auto split: sum.splits)
  subgoal for t by (auto split: sum.splits) .

lemma D_closed_sswapD: "dt \<in> D<+>UNIV \<Longrightarrow> sswapD dt x y \<in> D<+>UNIV" 
apply(cases dt)
  subgoal for d using D_closed_swapD[of d] by (auto split: sum.splits)
  subgoal for t by (auto split: sum.splits) .

lemma Dest_Lm_NE: "Dest t = Ll K \<Longrightarrow> K \<noteq> {}"
unfolding Dest_def apply(cases t, auto split: if_splits)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
using is_Lm_def2 by blast

lemma DDestD_LmD_NE: "dt \<in> D<+>UNIV \<Longrightarrow> DDestD dt = Ll K \<Longrightarrow> K \<noteq> {}" 
apply(cases dt)
  subgoal for d using DestD_LmD_NE[of d] Dest_Lm_NE by (fastforce split: sum.splits) 
  subgoal for t using Dest_Lm_NE[of t] by (auto split: sum.splits) .

lemma ffreshD_DDestD_VrD: 
"dt \<in> D<+>UNIV \<Longrightarrow> ffreshD z dt \<Longrightarrow> DDestD dt = Vv x \<Longrightarrow> z \<noteq> x"
apply(cases dt)
  subgoal for d using FrVrI[of d] fresh_Dest_Vr freshD_DestD_trm 
  by (fastforce split: sum.splits) 
  subgoal for t using fresh_Dest_Vr by (auto split: sum.splits) .

lemma ffreshD_DDestD_ApD: 
"dt \<in> D<+>UNIV \<Longrightarrow> ffreshD z dt \<Longrightarrow> DDestD dt = Aa (dt1,dt2)
  \<Longrightarrow> ffreshD z dt1 \<and> ffreshD z dt2"
apply(cases dt)
  subgoal for d  
  apply (auto split: sum.splits) 
  using FrApI[of d _ ] fresh_Dest_Ap freshD_DestD_trm 
  by (metis comp_eq_dest_lhs)+
  subgoal for t 
  apply (auto split: sum.splits)
  using fresh_Dest_Ap[of _ t]  
  by (metis comp_eq_dest_lhs)+ .

lemma freshD_DDestD_LmD: 
"ddt \<in> D<+>UNIV \<Longrightarrow> ffreshD z ddt \<Longrightarrow> DDestD ddt = Ll K \<Longrightarrow> (x,dt) \<in> K \<Longrightarrow> 
 (z = x \<or> ffreshD z dt)"
apply(cases ddt)
  subgoal for d   
  apply (auto split: sum.splits) 
  using FrLmI[of d _ ] fresh_Dest_Lm freshD_DestD_trm 
  by (metis (no_types, lifting) comp_apply)+
  subgoal for t 
  apply (auto split: sum.splits)
  using fresh_Dest_Lm[of _ t]  
  by (metis (no_types, lifting) comp_apply)+ . 

lemma sswapD_DDestD_VrD: "dt \<in> D<+>UNIV \<Longrightarrow> 
  DDestD dt = Vv x \<Longrightarrow> DDestD (sswapD dt z1 z2) = Vv (sw x z1 z2)"
apply(cases dt)
  subgoal for d   
  apply (auto split: sum.splits) 
  using SwVrI[of d] swap_Dest_Vr swapD_DestD_trm by auto
  subgoal for t using swap_Dest_Vr
  by (auto split: sum.splits) .

lemma sswapD_DDestD_ApD: "dt \<in> D<+>UNIV \<Longrightarrow>
  DDestD dt = Aa (dt1,dt2) \<Longrightarrow> 
  DDestD (sswapD dt z1 z2) = Aa (sswapD dt1 z1 z2, sswapD dt2 z1 z2)"
apply(cases dt)
  subgoal for d   
  apply (auto split: sum.splits) 
  using SwApI[of d] swap_Dest_Ap swapD_DestD_trm by auto
  subgoal for t using swap_Dest_Ap
  by (auto split: sum.splits) .

lemma swapD_DDestD_LmD: 
"DDestD ddt = Ll K \<Longrightarrow> ddt \<in> D<+>UNIV \<Longrightarrow>
  \<exists>K'. DDestD (sswapD ddt z1 z2) = Ll K' \<and>  
  (\<forall>x dt. (x,dt) \<in> K \<longrightarrow> (sw x z1 z2, sswapD dt z1 z2) \<in> K')"
apply(cases ddt)
  subgoal for dd   
  apply (auto split: sum.splits) 
  using SwLmI[of dd] swap_Dest_Lm swapD_DestD_trm apply auto 
  apply (metis (no_types, lifting) Inr_not_Inl old.sum.inject(1))
  apply (metis (no_types, lifting) Inl_Inr_False Inl_inject sum.inject(2))
  apply (metis (no_types, opaque_lifting) Inl_inject old.sum.inject(2))
  apply (metis Inr_Inl_False)
  apply (metis old.sum.distinct(1))
  apply (metis old.sum.distinct(1))
  apply (metis Inr_Inl_False swap_Dest_Vr swap_idem)
  apply (metis (no_types, opaque_lifting) Inr_not_Inl sum.inject(2))
  by (metis (no_types, opaque_lifting) old.sum.inject(2)) 
  
  subgoal for t using swap_Dest_Lm
  apply (auto split: sum.splits)  
  apply (metis Inr_Inl_False swap_Dest_Vr swap_idem)
  apply (metis (no_types, opaque_lifting) Inl_Inr_False old.sum.inject(2))
  by (metis (no_types, opaque_lifting) sum.inject(2)) .

lemma nswappingOn_sswapD:  
"nswappingOn (D<+>UNIV) sswapD"
unfolding nswappingOn_def apply(intro allI conjI impI)
  subgoal for dt x
  using nswappingFresh_swapD_freshD unfolding nswappingOn_def 
  apply(cases dt) by auto 
  subgoal for dt x y
  apply(cases dt) apply auto
  using nswappingFresh_swapD_freshD unfolding nswappingOn_def by auto
  subgoal for x y dt z1 z2
  apply(cases dt) apply simp
  using nswappingFresh_swapD_freshD  unfolding nswappingOn_def  
  apply blast using swap_cmpTrans by auto . 

lemma swappingSwFrOn_sswapD_ffreshD:  
"swappingSwFrOn (D<+>UNIV) sswapD ffreshD"
unfolding swappingSwFrOn_def apply(intro allI conjI impI)
  subgoal for dt x y
  apply(cases dt) 
  using nswappingFresh_swapD_freshD swap_fresh_eq unfolding swappingSwFrOn_def by auto .

lemma DRnBvrI: 
"ddt \<in> D<+>UNIV \<Longrightarrow> DDestD ddt = Ll K \<Longrightarrow> {(x,dt),(x',dt')} \<subseteq> K \<Longrightarrow> 
 (x' = x \<or> ffreshD x' dt) \<and> sswapD dt x' x = dt'"
apply(cases ddt)
  subgoal for dd   
  apply (auto split: sum.splits) 
  using RnBvrI[of dd] Dest_Lm_rename swapD_DestD_trm 
  by auto blast+
  subgoal for t using Dest_Lm_rename[of t]  apply (auto split: sum.splits)
  by blast .

end (* context SwapFreshV_comodel_setBased_full *)

sublocale SwapFreshV_comodel_setBased_full < IT: SwapFreshV_comodel_setBased
where D = "D<+>UNIV " and DestD = DDestD and swapD = sswapD and freshD = ffreshD
apply standard 
  subgoal by simp
  subgoal using D_closed_DDestD_ApD .
  subgoal using D_closed_DDestD_LmD .
  subgoal using D_closed_sswapD .
  subgoal using DDestD_LmD_NE .
  subgoal using ffreshD_DDestD_VrD .
  subgoal using ffreshD_DDestD_ApD .
  subgoal using freshD_DDestD_LmD .
  subgoal using sswapD_DDestD_VrD .
  subgoal using sswapD_DDestD_ApD .
  subgoal using swapD_DDestD_LmD .
  subgoal using nswappingOn_sswapD swappingSwFrOn_sswapD_ffreshD by simp
  subgoal using DRnBvrI . .


end


