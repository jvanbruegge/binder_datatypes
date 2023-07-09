theory Generic_Barendregt_Enhanced_Rule_Induction
imports Main "MRBNF_Recursor"
begin 

declare [[inductive_internals]]

(* consts largeEnough :: "'a \<Rightarrow> bool"

class largeEnough = 
assumes "largeEnough (undefined::'a)" *)

(* General infrastructure: *)
locale Small = 
fixes dummy :: "'A"
assumes inf_A: "infinite (UNIV::'A set)" 
and reg_A: "regularCard |UNIV::'A set|"
begin 

definition small :: "'A set \<Rightarrow> bool" where 
"small A \<equiv> |A| <o |UNIV::'A set|"(* small/bounded sets *)
definition ssbij :: "('A \<Rightarrow> 'A) \<Rightarrow> bool" (* small-support bijections *) where 
"ssbij \<sigma> \<equiv> bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::'A set|"

lemma small_Un: "small A \<Longrightarrow> small B \<Longrightarrow> small (A \<union> B)"
using Un_bound small_def Small_axioms Small_def by blast

lemma finite_UN_small:
assumes "finite As" and "\<And>A. A \<in> As \<Longrightarrow> small A"
shows "small (\<Union> As)"
using assms apply(induct As)  
using small_Un by (auto simp: inf_A small_def)

lemma ssbij_bij: "\<And>\<sigma>. ssbij \<sigma> \<Longrightarrow> bij \<sigma>"
unfolding ssbij_def by auto

lemma ssbij_id: "ssbij id" unfolding ssbij_def bij_def  
  by (simp add: supp_id_bound)

lemma ssbij_comp: "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> ssbij (\<sigma> o \<tau>)"
by (meson Small_axioms Small_def bij_comp ssbij_def supp_comp_bound)

lemma ssbij_inv: "\<And>\<sigma>. ssbij \<sigma> \<Longrightarrow> ssbij (inv \<sigma>)"
by (simp add: ssbij_def supp_inv_bound)


lemma small_ssbij: 
assumes s: "small A" "small B" "small A'" "A \<inter> A' = {}"
shows "\<exists>\<sigma>. ssbij \<sigma> \<and> \<sigma> ` A \<inter> B = {} \<and> (\<forall>a\<in>A'. \<sigma> a = a)"
proof-
  obtain D where D: "D \<inter> B = {}" "D \<inter> A = {}" "D \<inter> A' = {}" and DA: "|D| =o |A|"
  using exists_subset_compl[of _ A "A' \<union> B"]  
  by (metis Field_card_of Int_Un_emptyI1 Int_Un_emptyI2 Int_commute card_of_Card_order card_of_UNIV 
   cinfinite_def inf_A ordIso_symmetric s(1-3) small_Un small_def)  

  then obtain u where u: "bij_betw u A D"  
  using card_of_ordIso ordIso_symmetric by blast
  hence u: "u ` A = D" "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> u a = u b \<longleftrightarrow> a = b"
  unfolding bij_betw_def inj_on_def by auto

  let ?iu = "inv_into A u" 
  have iu: "bij_betw ?iu D A"
  using u by (metis bij_betw_def bij_betw_inv_into inj_on_def)
  hence iu: "?iu ` D = A" "\<And>a b. a \<in> D \<Longrightarrow> b \<in> D \<Longrightarrow> ?iu a = ?iu b \<longleftrightarrow> a = b"
  unfolding bij_betw_def inj_on_def by auto

  define v where "v \<equiv> \<lambda>a. if a \<in> A then u a else if a \<in> D then ?iu a else a"
  have v[simp]: "\<And>a. a \<in> A \<Longrightarrow> v a = u a" "\<And>a. a \<in> D \<Longrightarrow> v a = ?iu a"
  "\<And>a. a \<notin> A \<and> a \<notin> D \<Longrightarrow> v a = a"
  using D(2) unfolding v_def by auto

  have cas: "\<And>a. a \<in> A \<or> a \<in> D \<or> (a \<notin> A \<and> a \<notin> D)" by auto

  have bv: "bij v"
  unfolding bij_def inj_def image_def apply auto 
  apply (metis (mono_tags, lifting) D(2) Int_emptyD f_inv_into_f imageI iu(1) u(1) u(2) v_def)
  by (metis f_inv_into_f inv_into_into iu(1) u(1) v(2) v_def) 

  have sv: "supp v \<subseteq> A \<union> D" unfolding supp_def using v(3) by blast

  show ?thesis apply(rule exI[of _ v], intro conjI)
    subgoal using bv sv s(1) unfolding ssbij_def small_def 
      by (meson DA card_of_Un_ordLess_infinite card_of_subset_bound inf_A ordIso_ordLess_trans)
    subgoal using D(1) u(1) by auto
    subgoal using sv D(3) s(4) unfolding supp_def by auto . 
qed


lemma ssbij_invL: "ssbij \<sigma> \<Longrightarrow> \<sigma> o inv \<sigma> = id"
by (meson bij_is_surj ssbij_bij surj_iff)

lemma ssbij_invL': "ssbij \<sigma> \<Longrightarrow> \<sigma> (inv \<sigma> a) = a"
using ssbij_invL pointfree_idE by fastforce

lemma ssbij_invR: "ssbij \<sigma> \<Longrightarrow> inv \<sigma> o \<sigma> = id"
by (meson bij_def inv_o_cancel ssbij_bij)

lemma ssbij_invR': "ssbij \<sigma> \<Longrightarrow> inv \<sigma> (\<sigma> a) = a"
using ssbij_invR pointfree_idE by fastforce

 
end (* contaxt Small *)


locale Components = Small dummy 
for dummy :: 'A 
+
fixes (* 'T: term-like entities *)
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
(* 'V: variable-binding entities (essentially, binders) *)
and Vmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'V \<Rightarrow> 'V"
and Vfvars :: "'V \<Rightarrow> 'A set"
assumes  
Tmap_id: "Tmap id = id"
and 
Tmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) = Tmap \<sigma> o Tmap \<tau>"
and 
small_Tfvars: "\<And>t. small (Tfvars t)" 
and (* the weaker, inclusion-based version is sufficient (and similarly for V): *)
Tmap_Tfvars: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> Tfvars (Tmap \<sigma> t) \<subseteq> \<sigma> ` (Tfvars t)"
and 
Tmap_cong_id: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Tfvars t. \<sigma> a = a) \<Longrightarrow> Tmap \<sigma> t = t"
(* *)
and 
(* : "Vmap id = id" (not needed)
and *)
Vmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) = Vmap \<sigma> o Vmap \<tau>"
and 
small_Vfvars: "\<And>v. small (Vfvars v)" 
and 
Vmap_Vfvars: "\<And>v \<sigma>. ssbij \<sigma> \<Longrightarrow> Vfvars (Vmap \<sigma> v) \<subseteq> \<sigma> ` (Vfvars v)"
(* *)
(* *)
begin

lemma Tmap_comp': "\<And>\<sigma> \<tau> t. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) t = Tmap \<sigma> (Tmap \<tau> t)"
using Tmap_comp by fastforce 

lemma Vmap_comp': "\<And>\<sigma> \<tau> v. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) v = Vmap \<sigma> (Vmap \<tau> v)"
using Vmap_comp by fastforce

lemma Vfvars_Tfvars_disj: "ssbij \<sigma> \<Longrightarrow> Vfvars v \<inter> Tfvars t = {} \<Longrightarrow> Vfvars (Vmap \<sigma> v) \<inter> Tfvars (Tmap \<sigma> t) = {}"
apply(frule Vmap_Vfvars[of _ v]) apply(frule Tmap_Tfvars[of _ t])  
apply(drule ssbij_bij)    
by auto (metis Int_iff bij_inv_eq_iff emptyE imageE insert_absorb insert_subset)

(* *)

end (* locale Components *)


locale Induct1 = Components dummy Tmap Tfvars Vmap Vfvars 
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Vmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'V \<Rightarrow> 'V"
and Vfvars :: "'V \<Rightarrow> 'A set"
+
fixes (* The operator that defines the inductive predicate as lfp:  *)
G :: "('T \<Rightarrow> bool) \<Rightarrow> 'V \<Rightarrow> 'T \<Rightarrow> bool"
assumes 
G_mono[mono]: "\<And>R R' v t. R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
and 
G_equiv: "\<And>\<sigma> R v t. ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
begin

lemma G_mono'[mono]: "\<And>R R' v t.  R \<le> R' \<Longrightarrow> G R v t \<longrightarrow> G R' v t"
  using G_mono by blast

inductive I :: "'T \<Rightarrow> bool" where 
G_I_intro: "G I v t \<Longrightarrow> I t"

lemma "I \<equiv> lfp (\<lambda>R t. \<exists>v. G R v t)"
using I_def[simplified] .

(*
(*  Not needed: *) 
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
(* *)
*)

inductive I' :: "'T \<Rightarrow> bool" where 
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

definition GG where "GG R \<equiv> G (\<lambda>t. I' t \<and> R t)"

lemma GG_imp_G: "GG R v t \<Longrightarrow> G R v t" 
unfolding GG_def by (metis (no_types, lifting) G_mono predicate1I)

lemma GG_mono[mono]: "R \<le> R' \<Longrightarrow> GG R v t \<Longrightarrow> GG R' v t"
unfolding GG_def using G_mono[of "\<lambda>t. I' t \<and> R t" "\<lambda>t. I' t \<and> R' t"] by auto

lemma GG_mono'[mono]: "\<And>R R' v t.  R \<le> R' \<Longrightarrow> GG R v t \<longrightarrow> GG R' v t"
  using GG_mono by blast

lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> GG R v t \<Longrightarrow> GG (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
unfolding GG_def using G_equiv[of \<sigma> "\<lambda>t. I' t \<and> R t" v t] I'_equiv[of _ \<sigma>]   
by simp (smt (z3) G_mono Tmap_comp' Tmap_id id_apply predicate1I ssbij_inv ssbij_invL)

inductive II' :: "'T \<Rightarrow> bool" where 
GG_II'_intro: "Vfvars v \<inter> Tfvars t = {} \<Longrightarrow> GG II' v t \<Longrightarrow> II' t"

lemma II'_I': "II' = I'"
apply(intro ext iffI)
  subgoal for t apply(induct rule: II'.induct)
  unfolding GG_def  
  by (metis (no_types, lifting) G_mono I'.intros predicate1I)
  subgoal for t apply(induct rule: I'.induct)
  by (auto simp: GG_def intro: II'.intros) .
  
end (* context Induct1 *)


locale Induct_enhanced = Induct1 dummy Tmap Tfvars Vmap Vfvars G
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Vmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'V \<Rightarrow> 'V"
and Vfvars :: "'V \<Rightarrow> 'A set"
and 
G :: "('T \<Rightarrow> bool) \<Rightarrow> 'V \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
GG_fresh: 
"\<And>R v t. (\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> GG R v t \<Longrightarrow> 
         \<exists>w. Vfvars w \<inter> Tfvars t = {} \<and> GG R w t"


locale Induct = Induct1 dummy Tmap Tfvars Vmap Vfvars G
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Vmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'V \<Rightarrow> 'V"
and Vfvars :: "'V \<Rightarrow> 'A set"
and 
G :: "('T \<Rightarrow> bool) \<Rightarrow> 'V \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
(* This one, in the style of Urban-Berghofer-Norrish, does not cover cases of interest, 
including beta-reduction (see their paper): 
G_fresh: "\<And>R v t. G R v t \<Longrightarrow> Vfvars v \<inter> Tfvars t = {}"
I replace it with a much weaker condition: namely that such a fresh v can be produced 
for equivariant relations R:  
*)
G_fresh: 
"\<And>R v t. (\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> G R v t \<Longrightarrow> 
         \<exists>w. Vfvars w \<inter> Tfvars t = {} \<and> G R w t"


sublocale Induct_enhanced < E: Induct where G = GG
apply standard
  subgoal using GG_mono .
  subgoal using GG_equiv .
  subgoal using GG_fresh . .

(* The locale with the more restricted rule, in the style of Urban-Berghofer-Norrish: *)
locale Induct_simple = Induct1 dummy Tmap Tfvars Vmap Vfvars G 
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Vmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'V \<Rightarrow> 'V"
and Vfvars :: "'V \<Rightarrow> 'A set"
and 
G :: "('T \<Rightarrow> bool) \<Rightarrow> 'V \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
G_fresh_simple: "\<And>R v t. G R v t \<Longrightarrow> Vfvars v \<inter> Tfvars t = {}"

sublocale Induct_simple < Induct apply standard
  subgoal using G_fresh_simple by blast . 


context Induct
begin

(* NB: The following could replace G_fresh in the axiomatization. 
It has the advantage that it is weaker, but also two disadvantages:
-- it depends on the "auxiliary" defined predicate I'
-- the dependency on I' seems truly inessential, in that in concrete cases 
all that one needs to use is the equivariance of I'
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

(* PP: parameters *) 

theorem BE_induct[consumes 2]: 
(* Parameters: *)
fixes Pfvars :: "'P \<Rightarrow> 'A set"
assumes small_Pfvars: "\<And>p. small (Pfvars p)" 
(* *)
assumes I: "I (t::'T)"
and strong: "\<And> p v t. Vfvars v \<inter> Pfvars p = {} \<Longrightarrow> Vfvars v \<inter> Tfvars t = {} \<Longrightarrow> 
      G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) v t \<Longrightarrow> R p t"
shows "R p t"
proof- 
  {fix \<sigma> assume \<sigma>: "ssbij \<sigma>"
   have "R p (Tmap \<sigma> t)"
   using I \<sigma> unfolding I_eq_I' proof(induct arbitrary: \<sigma> p)
     fix v t \<sigma> p 
     assume vt: "Vfvars v \<inter> Tfvars t = {}" (* this additional vt assumption is what we have gained 
     by transitioning from I to I', whose inductive definition has this freshness side-condition *)
     and G: "G (\<lambda>t'. I' t' \<and> (\<forall>\<sigma>'. ssbij \<sigma>' \<longrightarrow> (\<forall>p'. R p' (Tmap \<sigma>' t')))) v t" and \<sigma>: "ssbij \<sigma>" 

     define v' where v': "v' \<equiv> Vmap \<sigma> v"

     have v't: "Vfvars v' \<inter> Tfvars (Tmap \<sigma> t) = {}" 
     using vt unfolding v'  
     using Vfvars_Tfvars_disj \<sigma> by blast 

     have small_p_t: "small (Pfvars p \<union> Tfvars (Tmap \<sigma> t))"  
       by (simp add: small_Pfvars small_Tfvars small_Un)

     obtain \<rho> where \<rho>: "ssbij \<rho>" "\<rho> ` (Vfvars v') \<inter> (Pfvars p \<union> Tfvars (Tmap \<sigma> t)) = {}" "\<forall>a \<in> Tfvars (Tmap \<sigma> t). \<rho> a = a"
     using small_ssbij small_Tfvars small_Vfvars  small_p_t v't by metis

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
     using I'_equiv[OF _ ss_\<sigma>''] 
     by (smt (verit, del_insts) G_mono predicate1I) 
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

end (* context Induct *)


context Induct_enhanced 
begin

lemma E_I: "E.I = I"
apply(intro ext iffI)
  subgoal for t apply(induct rule: E.I.induct) 
  by (metis (mono_tags, lifting) GG_def G_mono I.intros predicate1I)
  subgoal for t apply(induct rule: I.induct) 
  by (smt (verit, best) E.I'.simps E.I.simps E.I_eq_I' GG_def G_mono' II'.intros II'_I' predicate1I) .



theorem BE_induct_enhanced[consumes 2]: 
(* Parameters: *)
fixes Pfvars :: "'P \<Rightarrow> 'A set"
assumes small_Pfvars: "\<And>p. small (Pfvars p)" 
(* *)
assumes I: "I (t::'T)"
and strong: "\<And> p v t. Vfvars v \<inter> Pfvars p = {} \<Longrightarrow> Vfvars v \<inter> Tfvars t = {} \<Longrightarrow> 
      G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) v t \<Longrightarrow> R p t"
shows "R p t"
apply(rule E.BE_induct[unfolded E_I, OF small_Pfvars I, of _ R])
using strong GG_imp_G by blast


end (* context Induct_enhanced *)


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