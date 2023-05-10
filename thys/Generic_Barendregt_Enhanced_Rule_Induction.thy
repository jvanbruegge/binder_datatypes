theory Generic_Barendregt_Enhanced_Rule_Induction
imports Main
begin 

consts laregeEnough :: "'a \<Rightarrow> bool"

class largeEnough =
assumes "largeEnough (undefined::'a)"

(* General infrastructure: *)
consts small :: "('a::largeEnough) set \<Rightarrow> bool" (* small/bounded sets *)
consts ssbij :: "(('a::largeEnough)\<Rightarrow>'a) \<Rightarrow> bool" (* small-support bijections *)

axiomatization where 
ssbij_bij: "\<And>\<sigma>. ssbij \<sigma> \<Longrightarrow> bij \<sigma>"
and 
ssbij_id: "ssbij id"
and 
ssbij_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> ssbij (\<sigma> o \<tau>)"
and 
ssbij_inv: "\<And>\<sigma>. ssbij \<sigma> \<Longrightarrow> ssbij (inv \<sigma>)"
and 
small_ssbij: "\<And> A B. small A \<Longrightarrow> small B \<Longrightarrow> \<exists>\<sigma>. ssbij \<sigma> \<and> \<sigma> ` A \<inter> A = {} \<and> (\<forall>b\<in>B. \<sigma> b = b)"

lemma ssbij_invL: "ssbij \<sigma> \<Longrightarrow> \<sigma> o inv \<sigma> = id"
by (meson bij_is_surj ssbij_bij surj_iff)
lemma ssbij_invL': "ssbij \<sigma> \<Longrightarrow> \<sigma> (inv \<sigma> a) = a"
using ssbij_invL pointfree_idE by fastforce
(* *)
lemma ssbij_invR: "ssbij \<sigma> \<Longrightarrow> inv \<sigma> o \<sigma> = id"
by (meson bij_def inv_o_cancel ssbij_bij)
lemma ssbij_invR': "ssbij \<sigma> \<Longrightarrow> inv \<sigma> (\<sigma> a) = a"
using ssbij_invR pointfree_idE by fastforce


typedecl 'a T (* term-like entities *)
consts Tmap :: "(('a::largeEnough)\<Rightarrow>'a) \<Rightarrow> 'a T \<Rightarrow> 'a T"
consts Tsupp :: "('a::largeEnough) T \<Rightarrow> 'a set"

typedecl 'a V (* variable-binding entities (essentially, binders) *)
consts Vmap :: "(('a::largeEnough)\<Rightarrow>'a) \<Rightarrow> 'a V \<Rightarrow> 'a V"
consts Vsupp :: "('a::largeEnough) V \<Rightarrow> 'a set"

typedecl 'a P (* parameters *)
consts Psupp :: "('a::largeEnough) P \<Rightarrow> 'a set"

axiomatization where 
Tmap_id: "Tmap id = id"
and 
Tmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) = Tmap \<sigma> o Tmap \<tau>"
and 
small_Tsupp: "\<And>t. small (Tsupp t)" 
and 
Tmap_Tsupp: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> Tsupp (Tmap \<sigma> t) \<subseteq> \<sigma> ` (Tsupp t)"
and 
Tmap_cong_id: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Tsupp t. \<sigma> a = a) \<Longrightarrow> Tmap \<sigma> t = t"

lemma Tmap_comp': "\<And>\<sigma> \<tau> t. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) t = Tmap \<sigma> (Tmap \<tau> t)"
using Tmap_comp by fastforce

axiomatization where 
Vmap_id: "Vmap id = id"
and 
Vmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) = Vmap \<sigma> o Vmap \<tau>"
and 
small_Vsupp: "\<And>v. small (Vsupp v)" 
and 
Vmap_Vsupp: "\<And>v \<sigma>. ssbij \<sigma> \<Longrightarrow> Vsupp (Vmap \<sigma> v) \<subseteq> \<sigma> ` (Vsupp v)"

lemma Vmap_comp': "\<And>\<sigma> \<tau> v. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) v = Vmap \<sigma> (Vmap \<tau> v)"
using Vmap_comp by fastforce

axiomatization where  
small_Psupp: "\<And>p. small (Psupp p)" 


(* *)

consts G :: "('a T \<Rightarrow> bool) \<Rightarrow> ('a::largeEnough) T \<Rightarrow> 'a V \<Rightarrow> bool"

axiomatization where 
G_equiv: "\<And>\<sigma> R t v. ssbij \<sigma> \<Longrightarrow> G R t v \<Longrightarrow> G (\<lambda>t'. R (Tmap \<sigma> t')) (Tmap \<sigma> t) (Vmap \<sigma> v)"
and 
G_fresh: "\<And>R t v. G R t v \<Longrightarrow> Vsupp v \<inter> Tsupp t = {}"
and 
G_mono[mono]: "\<And>R R' t v. R \<le> R' \<Longrightarrow> G R t v \<longrightarrow> G R' t v"

(* *)

inductive I :: "('a::largeEnough) T \<Rightarrow> bool" where 
G_I_intro: "G I t v \<Longrightarrow> I t"

lemma I_equiv: 
assumes "I t" and "ssbij \<sigma>"
shows "I (Tmap \<sigma> t)"
using assms apply induct  
by (smt (z3) G_I_intro G_mono IntI Tmap_cong_id emptyE empty_subsetI imageI le_boolI' le_funI small_Tsupp small_ssbij)

(* Barendregt-enhanced (strong) induction: *)
lemma BE_induct: 
assumes I: "I (t::('a::largeEnough) T)"
and strong: "\<And> p t v. Vsupp v \<inter> Psupp p = {} \<and> G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) t v \<Longrightarrow> R p t"
shows "R p t"
proof-
  {fix \<sigma>::"'a\<Rightarrow>'a" assume \<sigma>: "ssbij \<sigma>"
   have "R p (Tmap \<sigma> t)"
   using I \<sigma> proof(induct arbitrary: \<sigma> p)
   fix t and v and \<sigma>::"'a\<Rightarrow>'a" and p 
   assume G: "G (\<lambda>t'. I t' \<and> (\<forall>\<sigma>'. ssbij \<sigma>' \<longrightarrow> (\<forall>p'. R p' (Tmap \<sigma>' t')))) t v" and \<sigma>: "ssbij \<sigma>" 

   define v' where v': "v' \<equiv> Vmap \<sigma> v"

   obtain \<rho> where \<rho>: "ssbij \<rho>" "\<rho> ` (Vsupp v') \<inter> Vsupp v' = {}" and 
   "\<forall>a \<in> Tsupp (Tmap \<sigma> t) \<union> Psupp p. \<rho> a = a"  
   	 using small_Vsupp small_Tsupp small_ssbij  
   	 by (metis Int_Un_eq(2) Int_iff all_not_in_conv image_eqI small_Psupp)
   hence "Tmap \<rho> (Tmap \<sigma> t) = Tmap \<sigma> t"  
     by (simp add: Tmap_cong_id)
   hence 0: "Tmap (\<rho> o \<sigma>) t = Tmap \<sigma> t" 
   	 by (simp add: Tmap_comp' \<rho>(1) \<sigma>)

   have \<rho>\<sigma>: "ssbij (\<rho> o \<sigma>)" by (simp add: \<rho>(1) \<sigma> ssbij_comp)

   define \<sigma>'' where \<sigma>'': "\<sigma>'' = inv \<sigma> o inv \<rho>"
   have ss_\<sigma>'': "ssbij \<sigma>''" using \<rho>(1) \<sigma> \<sigma>'' ssbij_comp ssbij_inv by blast
   
   have 1[simp]: "\<sigma>'' \<circ> \<rho> o \<sigma> = id" 
   unfolding \<sigma>'' by (simp add: \<rho>(1) \<sigma> rewriteR_comp_comp ssbij_invR)
   
   have "G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) t v" 
   apply(rule G_mono[rule_format, OF _ G]) using ss_\<sigma>'' by auto
   hence G: "G (\<lambda>t'. I (Tmap \<sigma>'' t') \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) t v" 
   using I_equiv[OF _ ss_\<sigma>''] by (metis (mono_tags, lifting) G_mono predicate1I)
   have G: "G (\<lambda>t'. I (Tmap \<sigma>'' (Tmap (\<rho> o \<sigma>) t')) \<and> (\<forall>p'. R p' (Tmap \<sigma>'' (Tmap (\<rho> o \<sigma>) t')))) (Tmap (\<rho> o \<sigma>) t) (Vmap (\<rho> o \<sigma>) v)" 
   using G_equiv[OF \<rho>\<sigma> G] .
   have G: "G (\<lambda>t'. I (Tmap (\<sigma>'' o \<rho> o \<sigma>) t') \<and> (\<forall>p'. R p' (Tmap (\<sigma>'' o \<rho> o \<sigma>) t'))) (Tmap \<sigma> t) (Vmap \<rho> v')" 
   unfolding v' Vmap_comp'[symmetric, OF \<rho>(1) \<sigma>] 0[symmetric] apply(rule G_mono[rule_format, OF _ G])  
   by auto (metis "1" Tmap_comp' \<rho>\<sigma> fun.map_comp ss_\<sigma>'')+ 
   have G: "G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) (Tmap \<sigma> t) (Vmap \<rho> v')" 
   apply(rule G_mono[rule_format, OF _ G]) 
   by (simp add: Tmap_id)
   
   have vv': "Vsupp (Vmap \<rho> v') \<inter> Psupp p = {}"  
     using small_Psupp small_ssbij by fastforce  

   show "R p (Tmap \<sigma> t)"
   apply(rule strong[of "Vmap \<rho> v'"], intro conjI)
     subgoal by fact
     subgoal by fact .
   qed
  }
  from this[of id] show ?thesis 
  by (simp add: Tmap_id ssbij_id)
qed



end 