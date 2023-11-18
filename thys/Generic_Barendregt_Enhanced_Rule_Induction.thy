theory Generic_Barendregt_Enhanced_Rule_Induction
imports Main "MRBNF_Recursor"
begin 

declare [[inductive_internals]]

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

lemma small_empty[simp,intro!]: "small {}"  
  by (simp add: inf_A small_def)

lemma small_singl[simp,intro!]: "small {x}" 
  by (simp add: inf_A small_def)

lemma small_two[simp,intro!]: "small {x,y}" 
  by (simp add: inf_A small_def)

lemma small_three[simp,intro!]: "small {x,y,z}" 
  by (simp add: inf_A small_def)

end (* context Small *)


locale Components = Small dummy 
for dummy :: 'A 
+
fixes (* 'T: term-like entities *)
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
(* (* 'V: variable-binding entities (essentially, binders) *)
and Vmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'V \<Rightarrow> 'V"
and Vfvars :: "'V \<Rightarrow> 'A set" *)
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
(* : "Vmap id = id" (not needed)
and *)
(* Vmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) = Vmap \<sigma> o Vmap \<tau>"
and 
small_Vfvars: "\<And>v. small (Vfvars v)" 
and 
Vmap_Vfvars: "\<And>v \<sigma>. ssbij \<sigma> \<Longrightarrow> Vfvars (image \<sigma> B) \<subseteq> \<sigma> ` (Vfvars v)" *)
(* *)
(* *)
begin

lemma Tmap_comp': "\<And>\<sigma> \<tau> t. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) t = Tmap \<sigma> (Tmap \<tau> t)"
using Tmap_comp by fastforce 

lemma small_image: "small B \<Longrightarrow> small (\<sigma> ` B)"
using card_of_image ordLeq_ordLess_trans small_def by blast

(* lemma image_comp': "\<And>\<sigma> \<tau> v. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) v = Vmap \<sigma> (Vmap \<tau> v)"
using Vmap_comp by fastforce

lemma image_Tfvars_disj: "ssbij \<sigma> \<Longrightarrow> Vfvars v \<inter> Tfvars t = {} \<Longrightarrow> Vfvars (image \<sigma> B) \<inter> Tfvars (Tmap \<sigma> t) = {}"
apply(frule Vmap_Vfvars[of _ v]) apply(frule Tmap_Tfvars[of _ t])  
apply(drule ssbij_bij)    
by auto (metis Int_iff bij_inv_eq_iff emptyE imageE insert_absorb insert_subset)
*)

lemmas image_comp' = image_comp[symmetric]

(*
lemma image_comp': "\<And>\<sigma> \<tau> B. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> image (\<sigma> o \<tau>) B = image \<sigma> (image \<tau> B)"
*)

lemma image_Tfvars_disj: "ssbij \<sigma> \<Longrightarrow> B \<inter> Tfvars t = {} \<Longrightarrow> image \<sigma> B \<inter> Tfvars (Tmap \<sigma> t) = {}"
using Tmap_Tfvars ssbij_bij by fastforce


(* *)

end (* locale Components *)


locale Induct1 = Components dummy Tmap Tfvars 
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
+
fixes (* The operator that defines the inductive predicate as lfp:  *)
G :: "('T \<Rightarrow> bool) \<Rightarrow> 'A set \<Rightarrow> 'T \<Rightarrow> bool"
assumes 
G_mono: "\<And>R R' B t. R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G R' B t"
and 
G_equiv: "\<And>\<sigma> R B t. ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (image \<sigma> B) (Tmap \<sigma> t)"
begin

lemma G_small_mono[mono]: "\<And>R R' B t.  R \<le> R' \<Longrightarrow> small B \<and> G R B t \<longrightarrow> small B \<and> G R' B t"
  using G_mono by blast

inductive I :: "'T \<Rightarrow> bool" where 
G_I_intro: "small B \<Longrightarrow> G I B t \<Longrightarrow> I t"

lemma "I \<equiv> lfp (\<lambda>R t. \<exists>B. small B \<and> G R B t)"
using I_def[simplified] .
 
lemma I_equiv: 
assumes "I t" and \<sigma>: "ssbij \<sigma>"
shows "I (Tmap \<sigma> t)"
using assms(1) proof induct 
  case (G_I_intro B t)   note B = G_I_intro(1)  
  have G: "G (\<lambda>t. I (Tmap \<sigma> t)) B t"
  apply(rule G_mono[OF _ G_I_intro(1,2)]) using \<sigma> by auto
  have G: "G (\<lambda>t. I (Tmap \<sigma> (Tmap (inv \<sigma>) t))) (image \<sigma> B) (Tmap \<sigma> t)"
  using G_equiv[OF \<sigma> B G] . 
  have "G I (image \<sigma> B) (Tmap \<sigma> t)" 
  apply(rule G_mono[OF _ _ G])
    subgoal using \<sigma> 
    by auto (metis Tmap_comp' Tmap_id id_apply ssbij_inv ssbij_invL)
    subgoal using small_image[OF B] . .
  thus ?case using small_image[OF B] by (subst I.simps, auto)
qed

lemma G_small_mono'[mono]: "\<And>R R' B t.  R \<le> R' \<Longrightarrow> 
 small B \<and> B \<inter> Tfvars t = {} \<and> G R B t \<longrightarrow> small B \<and> B \<inter> Tfvars t = {} \<and> G R' B t"
  using G_mono by blast

inductive I' :: "'T \<Rightarrow> bool" where 
G_I'_intro: "small B \<Longrightarrow> B \<inter> Tfvars t = {} \<Longrightarrow> G I' B t \<Longrightarrow> I' t"

lemma I'_imp_I: "I' t \<Longrightarrow> I t"
apply(induct rule: I'.induct)
by (smt (verit) G_mono I.simps predicate1I) 

lemma I'_equiv: 
assumes "I' t" and \<sigma>: "ssbij \<sigma>"
shows "I' (Tmap \<sigma> t)"
using assms(1) proof induct
  case (G_I'_intro B t)  note B = G_I'_intro(1,2)   
  have G: "G (\<lambda>t. I' (Tmap \<sigma> t)) B t"
  apply(rule G_mono[OF _ G_I'_intro(1,3)]) using \<sigma> by auto
  have BB: "image \<sigma> B \<inter> Tfvars (Tmap \<sigma> t) = {}" using image_Tfvars_disj[OF \<sigma> G_I'_intro(2)] .    
  have G: "G (\<lambda>t. I' (Tmap \<sigma> (Tmap (inv \<sigma>) t))) (image \<sigma> B) (Tmap \<sigma> t)"
  using G_equiv[OF \<sigma> B(1) G] .
  have 0: "(\<lambda>t. I' (Tmap \<sigma> (Tmap (inv \<sigma>) t))) = I'"
  unfolding fun_eq_iff  
  by (metis Tmap_comp' Tmap_cong_id \<sigma> id_apply ssbij_comp ssbij_inv ssbij_invL)
  have G: "G I' (image \<sigma> B) (Tmap \<sigma> t)"
  using G unfolding 0 .
  show ?case using BB G small_image[OF B(1)] by (subst I'.simps, auto) 
qed

end (* context Induct1 *)


locale Induct = Induct1 dummy Tmap Tfvars G
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and 
G :: "('T \<Rightarrow> bool) \<Rightarrow> 'A set \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
G_refresh: 
"\<And>R B t. (\<forall>t. R t \<longrightarrow> I t) \<Longrightarrow> 
         (\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> 
         \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G R C t"


context Induct
begin

(* NB: The following could replace G_refresh in the axiomatization. 
It has the advantage that it is weaker, but also two disadvantages:
-- it depends on the "auxiliary" defined predicate I'
-- the dependency on I' seems truly inessential, in that in concrete cases 
all that one needs to use is the equivariance of I'
Later note: in the end, if was useful for getting in inductive information, 
namely strenthening G_refresh to further assume that R implies I ("\<forall>t. R t \<longrightarrow> I t").  
 *)
lemma G_refresh_I': 
"\<And>B t. small B \<Longrightarrow> G I' B t \<Longrightarrow> \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G I' C t"
using G_refresh I'_equiv by (simp add: I'_imp_I)

lemma I_imp_I': "I t \<Longrightarrow> I' t"
proof(induct rule: I.induct)
  case (G_I_intro B t)
  hence G: "G I' B t" by (metis (no_types, lifting) G_mono predicate1I)
  note sB = `small B` 
  from G_refresh_I'[OF sB G]
  obtain C where 0: "small C" "C \<inter> Tfvars t = {}" "G I' C t" by auto 
  show ?case using I'.intros[OF 0] .
qed

lemma I_eq_I': "I = I'"
apply(rule ext)
subgoal for t
apply(rule iffI)
  subgoal using I_imp_I' by auto 
  subgoal using I'_imp_I by auto . .
 
end (* context Induct *)


(* The locale with the more restricted rule, in the style of Urban-Berghofer-Norrish: *)
locale Induct_simple = Induct1 dummy Tmap Tfvars G 
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and 
G :: "('T \<Rightarrow> bool) \<Rightarrow> 'A set \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
G_fresh: "\<And>R B t. small B \<Longrightarrow> G R B t \<Longrightarrow> B \<inter> Tfvars t = {}"

sublocale Induct_simple < Induct apply standard
  subgoal using G_fresh by blast . 


context Induct 
begin 
  
(* Barendregt-enhanced (strong) induction. 
NB: we get freshness for t as well, as a bonus (even though the inductive definition of I 
needs not guarantee that -- see again the case of beta-reduction)
 *)

theorem BE_induct[consumes 2]: 
(* Parameters: *)
fixes Pfvars :: "'P \<Rightarrow> 'A set"
assumes small_Pfvars: "\<And>p. small (Pfvars p)" 
(* *)
assumes I: "I (t::'T)"
and strong: "\<And> p B t. small B \<Longrightarrow> B \<inter> Pfvars p = {} \<Longrightarrow> B \<inter> Tfvars t = {} \<Longrightarrow> 
      G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) B t \<Longrightarrow> R p t"
shows "R p t"
proof- 
  {fix \<sigma> assume \<sigma>: "ssbij \<sigma>"
   have "R p (Tmap \<sigma> t)"
   using I \<sigma> unfolding I_eq_I' proof(induct arbitrary: \<sigma> p)
     fix B t \<sigma> p 
     assume small_B: "small B" and vt: "B \<inter> Tfvars t = {}" (* this additional vt assumption is what we have gained 
     by transitioning from I to I', whose inductive definition has this freshness side-condition *)
     and G: "G (\<lambda>t'. I' t' \<and> (\<forall>\<sigma>'. ssbij \<sigma>' \<longrightarrow> (\<forall>p'. R p' (Tmap \<sigma>' t')))) B t" and \<sigma>: "ssbij \<sigma>" 

     define B' where B': "B' \<equiv> image \<sigma> B"
     have small_B': "small B'"  
       using B' small_B small_image by blast

     have v't: "B' \<inter> Tfvars (Tmap \<sigma> t) = {}" 
     using vt unfolding B'  
     using image_Tfvars_disj \<sigma> by blast 

     have small_p_t: "small (Pfvars p \<union> Tfvars (Tmap \<sigma> t))"  
       by (simp add: small_Pfvars small_Tfvars small_Un)

     obtain \<rho> where \<rho>: "ssbij \<rho>" "image \<rho> B' \<inter> (Pfvars p \<union> Tfvars (Tmap \<sigma> t)) = {}" "\<forall>a \<in> Tfvars (Tmap \<sigma> t). \<rho> a = a"
     using small_ssbij[of B' "Pfvars p \<union> Tfvars (Tmap \<sigma> t)" "Tfvars (Tmap \<sigma> t)"] 
     using small_Tfvars small_B' small_p_t v't by metis

     have fresh_p: "image \<rho> B' \<inter> Pfvars p = {}" 
     and fresh_t: "image \<rho> B' \<inter> Tfvars (Tmap \<sigma> t) = {}"  
     using \<rho>(1,2) by auto

     hence "Tmap \<rho> (Tmap \<sigma> t) = Tmap \<sigma> t" 
     using Tmap_cong_id[OF \<rho>(1,3)] by blast
     hence 0: "Tmap (\<rho> o \<sigma>) t = Tmap \<sigma> t" 
   	 by (simp add: Tmap_comp' \<rho>(1) \<sigma>)

     have \<rho>\<sigma>: "ssbij (\<rho> o \<sigma>)" by (simp add: \<rho>(1) \<sigma> ssbij_comp)

     define \<sigma>'' where \<sigma>'': "\<sigma>'' = \<rho> o \<sigma>"
     have ss_\<sigma>'': "ssbij \<sigma>''" using \<rho>(1) \<sigma> \<sigma>'' ssbij_comp ssbij_inv by blast
   
     have 1[simp]: "\<sigma>'' \<circ> inv (\<rho> o \<sigma>) = id" 
     unfolding \<sigma>'' using \<rho>\<sigma> ssbij_invL by auto  
   
     have "G (\<lambda>t'. I' t' \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) B t"  
     apply(rule G_mono[OF _ small_B G]) using ss_\<sigma>'' by auto
     hence G: "G (\<lambda>t'. I' (Tmap \<sigma>'' t') \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) B t" 
     using I'_equiv[OF _ ss_\<sigma>'']  
     by (smt (verit, del_insts) G_mono predicate1I small_B) 
     have G: "G (\<lambda>t'. I' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')) \<and> (\<forall>p'. R p' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')))) 
                (image (\<rho> o \<sigma>) B) (Tmap (\<rho> o \<sigma>) t) " 
     using G_equiv[OF \<rho>\<sigma> small_B G] .
     

     have G: "G (\<lambda>t'. I' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t') \<and> (\<forall>p'. R p' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t'))) 
                (image \<rho> B') (Tmap \<sigma> t) "  
     unfolding B' unfolding image_comp 0[symmetric]
     apply(rule G_mono[OF _ _ G])
       subgoal by auto (metis "1" Tmap_comp' \<rho>\<sigma> ss_\<sigma>'' ssbij_inv)+
       subgoal by (simp add: small_B small_image) .

     have G: "G (\<lambda>t'. I' t' \<and> (\<forall>p'. R p' t')) (image \<rho> B') (Tmap \<sigma> t)" 
     apply(rule G_mono[OF _ _ G]) 
       subgoal by (simp add: Tmap_id)
       subgoal using small_image[OF small_B'] . .

     note sm = small_image[OF small_B']

     show "R p (Tmap \<sigma> t)" 
     using strong[OF sm fresh_p fresh_t G[unfolded I_eq_I'[symmetric]]] .
  qed
  }
  from this[of id] show ?thesis 
  by (simp add: Tmap_id ssbij_id)
qed

end (* context Induct *)


end 