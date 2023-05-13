theory Generic_Barendregt_Enhanced_Rule_Induction
imports Main
begin 

consts laregeEnough :: "'a \<Rightarrow> bool"

class largeEnough =
assumes "largeEnough (undefined::'a)"

(* General infrastructure: *)
consts small :: "('a::largeEnough) set \<Rightarrow> bool" (* small/bounded sets *)
consts ssbij :: "(('a::largeEnough)\<Rightarrow>'a) \<Rightarrow> bool" (* small-fvarsort bijections *)

axiomatization where 
ssbij_bij: "\<And>\<sigma>. ssbij \<sigma> \<Longrightarrow> bij \<sigma>"
and 
ssbij_id: "ssbij id"
and 
ssbij_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> ssbij (\<sigma> o \<tau>)"
and 
ssbij_inv: "\<And>\<sigma>. ssbij \<sigma> \<Longrightarrow> ssbij (inv \<sigma>)"
and 
small_ssbij: "\<And> A B A'. small A \<Longrightarrow> small B \<Longrightarrow> small A' \<Longrightarrow> A \<inter> A' = {} \<Longrightarrow> 
   \<exists>\<sigma>. ssbij \<sigma> \<and> \<sigma> ` A \<inter> B = {} \<and> (\<forall>a\<in>A'. \<sigma> a = a)"
 

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
consts Tfvars :: "('a::largeEnough) T \<Rightarrow> 'a set"

typedecl 'a V (* variable-binding entities (essentially, binders) *)
consts Vmap :: "(('a::largeEnough)\<Rightarrow>'a) \<Rightarrow> 'a V \<Rightarrow> 'a V"
consts Vfvars :: "('a::largeEnough) V \<Rightarrow> 'a set"

typedecl 'a P (* parameters *)
consts Pfvars :: "('a::largeEnough) P \<Rightarrow> 'a set"

axiomatization where 
Tmap_id: "Tmap id = id"
and 
Tmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) = Tmap \<sigma> o Tmap \<tau>"
and 
small_Tfvars: "\<And>t. small (Tfvars t)" 
and 
Tmap_Tfvars: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> Tfvars (Tmap \<sigma> t) \<subseteq> \<sigma> ` (Tfvars t)"
and 
Tmap_cong_id: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Tfvars t. \<sigma> a = a) \<Longrightarrow> Tmap \<sigma> t = t"

lemma Tmap_comp': "\<And>\<sigma> \<tau> t. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) t = Tmap \<sigma> (Tmap \<tau> t)"
using Tmap_comp by fastforce

axiomatization where 
Vmap_id: "Vmap id = id"
and 
Vmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) = Vmap \<sigma> o Vmap \<tau>"
and 
small_Vfvars: "\<And>v. small (Vfvars v)" 
and 
Vmap_Vfvars: "\<And>v \<sigma>. ssbij \<sigma> \<Longrightarrow> Vfvars (Vmap \<sigma> v) \<subseteq> \<sigma> ` (Vfvars v)"

lemma Vmap_comp': "\<And>\<sigma> \<tau> v. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) v = Vmap \<sigma> (Vmap \<tau> v)"
using Vmap_comp by fastforce

axiomatization where  
small_Pfvars: "\<And>p. small (Pfvars p)" 


(* *)

consts G :: "('a T \<Rightarrow> bool) \<Rightarrow> ('a::largeEnough) T \<Rightarrow> 'a V \<Rightarrow> bool"

axiomatization where 
G_mono[mono]: "\<And>R R' t v. R \<le> R' \<Longrightarrow> G R t v \<Longrightarrow> G R' t v"
and 
G_equiv: "\<And>\<sigma> R t v. ssbij \<sigma> \<Longrightarrow> G R t v \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t) (Vmap \<sigma> v)"
and 
(*
This was too strong (e.g., would not be true for disjuncts in the definition of G 
that do not deal with bound variables; also different bound variables for different disjoints 
could not be added to the top, to form a single var-structure v ): 
G_fresh: "\<And>R t v. G R t v \<Longrightarrow> Vfvars v \<inter> Tfvars t = {}"
and 
*)
(* "Operational" intuition for this next axiom: 
If a disjunct refers to the given variables, then these are fresh for t;
if it does not, then there is no dependency on that variable. 
*)
(*
G_var_equiv: "\<And>\<rho> R t v. (\<forall>a \<in> Tfvars t - Vfvars v. \<rho> a = a) \<Longrightarrow> ssbij \<rho> \<Longrightarrow> G R t v \<Longrightarrow> G R t (Vmap \<rho> v)"
*)
G_fresh: "\<And>R t v. G R t v \<Longrightarrow> Vfvars v \<inter> Tfvars t = {}"

(* *)

lemma G_mono'[mono]: "\<And>R R' t v. R \<le> R' \<Longrightarrow> G R t v \<longrightarrow> G R' t v"
  using G_mono by auto

inductive I :: "('a::largeEnough) T \<Rightarrow> bool" where 
G_I_intro: "G I t v \<Longrightarrow> I t"

thm nitpick_unfold(143)
lemma "I \<equiv> lfp (\<lambda>R t. \<exists>v. G R t v)"
  using nitpick_unfold(143) by auto

lemma I_equiv: 
assumes "I t" and "ssbij \<sigma>"
shows "I (Tmap \<sigma> t)"
using assms apply induct  (* SL-generated proof: *)
proof -
  fix ta :: "'a T" and v :: "'a V"
  assume a1: "G (\<lambda>x. I x \<and> (ssbij \<sigma> \<longrightarrow> I (Tmap \<sigma> x))) ta v"
  have "(\<lambda>t. I (Tmap (inv \<sigma>) t) \<and> (ssbij \<sigma> \<longrightarrow> I (Tmap \<sigma> (Tmap (inv \<sigma>) t)))) \<le> I"
    by (smt (z3) Tmap_comp' Tmap_id assms(2) id_apply predicate1I ssbij_inv ssbij_invL)
  then show "I (Tmap \<sigma> ta)"
    using a1 G_I_intro G_equiv G_mono assms(2) by blast
qed 

(* Barendregt-enhanced (strong) induction: *)
lemma BE_induct: 
assumes I: "I (t::('a::largeEnough) T)"
and strong: "\<And> p t v. Vfvars v \<inter> Pfvars p = {} \<Longrightarrow> G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) t v \<Longrightarrow> R p t"
shows "R p t"
proof-
  {fix \<sigma>::"'a\<Rightarrow>'a" assume \<sigma>: "ssbij \<sigma>"
   have "R p (Tmap \<sigma> t)"
   using I \<sigma> proof(induct arbitrary: \<sigma> p)
     fix t and v and \<sigma>::"'a\<Rightarrow>'a" and p 
     assume G: "G (\<lambda>t'. I t' \<and> (\<forall>\<sigma>'. ssbij \<sigma>' \<longrightarrow> (\<forall>p'. R p' (Tmap \<sigma>' t')))) t v" and \<sigma>: "ssbij \<sigma>" 

     define v' where v': "v' \<equiv> Vmap \<sigma> v"

     have "Vfvars v' \<inter> Tfvars (Tmap \<sigma> t) = {}" 
     unfolding v' using G_fresh[OF G_equiv[OF \<sigma> G]] .

     then obtain \<rho> where \<rho>: "ssbij \<rho>" "\<rho> ` (Vfvars v') \<inter> Pfvars p = {}" "\<forall>a \<in> Tfvars (Tmap \<sigma> t). \<rho> a = a"
     by (meson small_Pfvars small_Tfvars small_Vfvars small_ssbij)

     have fresh_p: "Vfvars (Vmap \<rho> v') \<inter> Pfvars p = {}"  
       using Vmap_Vfvars \<rho>(1) \<rho>(2) by blast 

     hence "Tmap \<rho> (Tmap \<sigma> t) = Tmap \<sigma> t" 
     using Tmap_cong_id[OF \<rho>(1,3)] by blast
     hence 0: "Tmap (\<rho> o \<sigma>) t = Tmap \<sigma> t" 
   	 by (simp add: Tmap_comp' \<rho>(1) \<sigma>)

     have \<rho>\<sigma>: "ssbij (\<rho> o \<sigma>)" by (simp add: \<rho>(1) \<sigma> ssbij_comp)

     define \<sigma>'' where \<sigma>'': "\<sigma>'' = \<rho> o \<sigma>"
     have ss_\<sigma>'': "ssbij \<sigma>''" using \<rho>(1) \<sigma> \<sigma>'' ssbij_comp ssbij_inv by blast
   
     have 1[simp]: "\<sigma>'' \<circ> inv (\<rho> o \<sigma>) = id" 
     unfolding \<sigma>''  
     using \<rho>\<sigma> ssbij_invL by auto  
   
     have "G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) t v" 
     apply(rule G_mono[rule_format, OF _ G]) using ss_\<sigma>'' by auto
     hence G: "G (\<lambda>t'. I (Tmap \<sigma>'' t') \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) t v" 
     using I_equiv[OF _ ss_\<sigma>''] by (metis (mono_tags, lifting) G_mono predicate1I)
     have G: "G (\<lambda>t'. I (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')) \<and> (\<forall>p'. R p' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')))) (Tmap (\<rho> o \<sigma>) t) (Vmap (\<rho> o \<sigma>) v)" 
     using G_equiv[OF \<rho>\<sigma> G] .
     have G: "G (\<lambda>t'. I (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t') \<and> (\<forall>p'. R p' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t'))) (Tmap \<sigma> t) (Vmap \<rho> v')" 
     unfolding v' Vmap_comp'[symmetric, OF \<rho>(1) \<sigma>] 0[symmetric] apply(rule G_mono[rule_format, OF _ G])
     apply auto by (metis "1" Tmap_comp' \<rho>\<sigma> ss_\<sigma>'' ssbij_inv)+  
     have G: "G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) (Tmap \<sigma> t) (Vmap \<rho> v')" 
     apply(rule G_mono[rule_format, OF _ G]) 
     by (simp add: Tmap_id)
   
     show "R p (Tmap \<sigma> t)" using strong[OF fresh_p G] . 
  qed
  }
  from this[of id] show ?thesis 
  by (simp add: Tmap_id ssbij_id)
qed





end 