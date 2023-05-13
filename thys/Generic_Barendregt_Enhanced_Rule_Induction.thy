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
small_Un: "\<And>A B. small A \<Longrightarrow> small B \<Longrightarrow> small (A \<union> B)"
and 
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

lemma Vfvars_Tfvars_disj: "ssbij \<sigma> \<Longrightarrow> Vfvars v \<inter> Tfvars t = {} \<Longrightarrow> Vfvars (Vmap \<sigma> v) \<inter> Tfvars (Tmap \<sigma> t) = {}"
apply(frule Vmap_Vfvars[of _ v]) apply(frule Tmap_Tfvars[of _ t])  
apply(drule ssbij_bij)  
by auto (metis Int_iff bij_inv_eq_iff emptyE imageE insert_absorb insert_subset)


(* *)

consts G :: "('a T \<Rightarrow> bool) \<Rightarrow> 'a V \<Rightarrow> ('a::largeEnough) T \<Rightarrow> bool"

axiomatization where 
G_mono[mono]: "\<And>R R' v t. R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
and 
G_equiv: "\<And>\<sigma> R v t. ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t) "
(* This one, in the style of Urban-Berghofer-Norrish, does not cover cases of interest, 
including beta-reduction (see their paper): 
G_fresh: "\<And>R v t. G R v t \<Longrightarrow> Vfvars v \<inter> Tfvars t = {}"
I replace it with a much weaker condition: namely that such a fresh v can be produced 
for equivariant relations R:  
*)
axiomatization where G_fresh: 
"\<And>R v t. (\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> G R v t \<Longrightarrow> 
         \<exists>w. Vfvars w  \<inter> Tfvars t = {} \<and> G R w t"

(* *)

lemma G_mono'[mono]: "\<And>R R' v t.  R \<le> R' \<Longrightarrow> G R v t \<longrightarrow> G R' v t"
  using G_mono by blast

inductive I :: "('a::largeEnough) T \<Rightarrow> bool" where 
G_I_intro: "G I v t \<Longrightarrow> I t"

thm nitpick_unfold(143)
lemma "I \<equiv> lfp (\<lambda>R t. \<exists>v. G R v t)"
  using nitpick_unfold(143) by auto

lemma I_equiv: 
assumes "I t" and "ssbij \<sigma>"
shows "I (Tmap \<sigma> t)"
using assms proof induct
  case (G_I_intro v t)   note \<sigma> = G_I_intro(2)
  have G: "G (\<lambda>t. I (Tmap \<sigma> t)) v t"
  apply(rule G_mono[OF _ G_I_intro(1)]) using \<sigma> by auto
  have G: "G (\<lambda>t. I (Tmap \<sigma> (Tmap (inv \<sigma>) t))) (Vmap \<sigma> v) (Tmap \<sigma> t)"
  using G_equiv[OF \<sigma> G] .
  have "G I (Vmap \<sigma> v) (Tmap \<sigma> t)" 
  apply(rule G_mono[OF _ G]) using \<sigma> 
    by auto (metis Tmap_comp' Tmap_id id_apply ssbij_inv ssbij_invL)
  thus ?case by(subst I.simps, auto)
qed

inductive I' :: "('a::largeEnough) T \<Rightarrow> bool" where 
G_I'_intro: "Vfvars v \<inter> Tfvars t = {} \<Longrightarrow> G I' v t \<Longrightarrow> I' t"

lemma I'_equiv: 
assumes "I' t" and "ssbij \<sigma>"
shows "I' (Tmap \<sigma> t)"
using assms proof induct
  case (G_I'_intro v t)   note \<sigma> = G_I'_intro(3)
  have G: "G (\<lambda>t. I' (Tmap \<sigma> t)) v t"
  apply(rule G_mono[OF _ G_I'_intro(2)]) using \<sigma> by auto
  have vv: "Vfvars (Vmap \<sigma> v) \<inter> Tfvars (Tmap \<sigma> t) = {}" using Vfvars_Tfvars_disj[OF \<sigma> G_I'_intro(1)] .   
  have G: "G (\<lambda>t. I' (Tmap \<sigma> (Tmap (inv \<sigma>) t))) (Vmap \<sigma> v) (Tmap \<sigma> t)"
  using G_equiv[OF \<sigma> G] .
  have G: "G I' (Vmap \<sigma> v) (Tmap \<sigma> t)" 
  apply(rule G_mono[OF _ G]) using \<sigma> 
    by auto (metis Tmap_comp' Tmap_id id_apply ssbij_inv ssbij_invL)
  show ?case using vv G by (subst I'.simps, auto) 
qed



(* NB: This could replace G_fresh in the axiomatization. 
It has the advantage that it is weaker, but also two disadvantages:
-- it depends on the "auxiliary" defined predicate I'
-- the dependency on I' seems truly inessentially, in that in concrete cases 
all that is need to check that is the equivariance of I'
 *)
lemma G_fresh_I': 
"\<And>v t. G I' v t \<Longrightarrow> \<exists>w. Vfvars w  \<inter> Tfvars t = {} \<and> G I' w t"
using G_fresh I'_equiv by blast

lemma I_imp_I': "I t \<Longrightarrow> I' t"
apply(induct rule: I.induct)
apply(subst I'.simps) 
by auto (metis (no_types, lifting) G_fresh_I' G_mono' predicate1I)


lemma I_eq_I': "I = I'"
apply(rule ext)
subgoal for t
apply(rule iffI)
  subgoal using I_imp_I' by auto 
  subgoal apply(induct rule: I'.induct)  
  by (smt (verit) G_mono' I.simps predicate1I) . .
  
  

(* Barendregt-enhanced (strong) induction. 
NB: we get freshness for t as well, as a bonus (even though the inductive definition of I 
needs not guarantee that -- see again the case of beta-reduction)
 *)
theorem BE_induct: 
assumes I: "I (t::('a::largeEnough) T)"
and strong: "\<And> p v t. Vfvars v \<inter> Pfvars p = {} \<Longrightarrow> Vfvars v \<inter> Tfvars t = {} \<Longrightarrow> 
      G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) v t \<Longrightarrow> R p t"
shows "R p t"
proof- 
  {fix \<sigma>::"'a\<Rightarrow>'a" assume \<sigma>: "ssbij \<sigma>"
   have "R p (Tmap \<sigma> t)"
   using I \<sigma> unfolding I_eq_I' proof(induct arbitrary: \<sigma> p)
     fix v t and \<sigma>::"'a\<Rightarrow>'a" and p 
     assume vt: "Vfvars v \<inter> Tfvars t = {}"
     and G: "G (\<lambda>t'. I' t' \<and> (\<forall>\<sigma>'. ssbij \<sigma>' \<longrightarrow> (\<forall>p'. R p' (Tmap \<sigma>' t')))) v t" and \<sigma>: "ssbij \<sigma>" 

     define v' where v': "v' \<equiv> Vmap \<sigma> v"

     have v't: "Vfvars v' \<inter> Tfvars (Tmap \<sigma> t) = {}" 
     using vt unfolding v'  
     using Vfvars_Tfvars_disj \<sigma> by blast 

     have small_p_t: "small (Pfvars p \<union> Tfvars (Tmap \<sigma> t))"  
       by (simp add: small_Pfvars small_Tfvars small_Un)

     then obtain \<rho> where \<rho>: "ssbij \<rho>" "\<rho> ` (Vfvars v') \<inter> (Pfvars p \<union> Tfvars (Tmap \<sigma> t)) = {}" "\<forall>a \<in> Tfvars (Tmap \<sigma> t). \<rho> a = a"
     by (meson small_Tfvars small_Vfvars small_ssbij v't) 

     have fresh_p: "Vfvars (Vmap \<rho> v') \<inter> Pfvars p = {}" 
     and fresh_t: "Vfvars (Vmap \<rho> v') \<inter> Tfvars (Tmap \<sigma> t) = {}"  
     using Vmap_Vfvars \<rho>(1) \<rho>(2) by blast+ 

     hence "Tmap \<rho> (Tmap \<sigma> t) = Tmap \<sigma> t" 
     using Tmap_cong_id[OF \<rho>(1,3)] by blast
     hence 0: "Tmap (\<rho> o \<sigma>) t = Tmap \<sigma> t" 
   	 by (simp add: Tmap_comp' \<rho>(1) \<sigma>)

     have \<rho>\<sigma>: "ssbij (\<rho> o \<sigma>)" by (simp add: \<rho>(1) \<sigma> ssbij_comp)

     define \<sigma>'' where \<sigma>'': "\<sigma>'' = \<rho> o \<sigma>"
     have ss_\<sigma>'': "ssbij \<sigma>''" using \<rho>(1) \<sigma> \<sigma>'' ssbij_comp ssbij_inv by blast
   
     have 1[simp]: "\<sigma>'' \<circ> inv (\<rho> o \<sigma>) = id" 
     unfolding \<sigma>'' using \<rho>\<sigma> ssbij_invL by auto  
   
     have "G (\<lambda>t'. I' t' \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) v t" 
     apply(rule G_mono[OF _ G]) using ss_\<sigma>'' by auto
     hence G: "G (\<lambda>t'. I' (Tmap \<sigma>'' t') \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) v t" 
     using I'_equiv[OF _ ss_\<sigma>''] by (metis (mono_tags, lifting) G_mono predicate1I)
     have G: "G (\<lambda>t'. I' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')) \<and> (\<forall>p'. R p' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')))) 
                (Vmap (\<rho> o \<sigma>) v) (Tmap (\<rho> o \<sigma>) t) " 
     using G_equiv[OF \<rho>\<sigma> G] .
     have G: "G (\<lambda>t'. I' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t') \<and> (\<forall>p'. R p' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t'))) 
                (Vmap \<rho> v') (Tmap \<sigma> t) " 
     unfolding v' Vmap_comp'[symmetric, OF \<rho>(1) \<sigma>] 0[symmetric] apply(rule G_mono[OF _ G])
     apply auto by (metis "1" Tmap_comp' \<rho>\<sigma> ss_\<sigma>'' ssbij_inv)+  
     have G: "G (\<lambda>t'. I' t' \<and> (\<forall>p'. R p' t')) (Vmap \<rho> v') (Tmap \<sigma> t)" 
     apply(rule G_mono[OF _ G]) 
     by (simp add: Tmap_id)

     show "R p (Tmap \<sigma> t)" 
     using strong[OF fresh_p fresh_t G[unfolded I_eq_I'[symmetric]]] .
  qed
  }
  from this[of id] show ?thesis 
  by (simp add: Tmap_id ssbij_id)
qed


(* 
Novel contribution: This principle is significantly more general than the one in 
Urban-Berghofer-Norrish:
- It is purely semantic, i.e., does not assume a fixed rigid format, where the assumptions 
of the rules are assumed to be of the form R t1 ... R tn
- Does not need to formalized meta-language to be epressed rigorously (they use "generic terms", 
quite non-rigorous presentation)
- It allows higher-order operators in rules
- Does not need to talk about explicit bindings, but handles everything via equivariance; 
this means that the result is not restricted to inductive rules for term-like entities
- It is really on par with standard Knaster-Tarski induction
- It covers more cases of interest (beta-reduction and the like), i.e., it makes formal 
their informal observation that in principle freshness can be assume there too, but that 
it is "annoying" they have to assume it. 

TODO: Formalize the Urban-Berghofer-Norrish result and show that it is a particular case of this. 
*)




end 