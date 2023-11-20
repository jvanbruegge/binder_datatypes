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

lemma small_image: "small B \<Longrightarrow> small (\<sigma> ` B)"
using card_of_image ordLeq_ordLess_trans small_def by blast

lemmas image_comp' = image_comp[symmetric]

end (* context Small *)


locale CComponents = Small dummy 
for dummy :: 'A 
+
fixes (* 'T: term-like entities, ranged over by t *)
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
      (* 'B: binder-like entities, ranged over by xs *)
and Bmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bvars :: "'B \<Rightarrow> 'A set"
(* well-formed binders: *)
and wfB :: "'B \<Rightarrow> bool" 
assumes  
Tmap_id[simp]: "Tmap id = id"
and 
Tmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) = Tmap \<sigma> o Tmap \<tau>"
and 
small_Tfvars: "\<And>t. small (Tfvars t)" 
and (* the weaker, inclusion-based version is sufficient (and similarly for B): *)
Tmap_Tfvars: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> Tfvars (Tmap \<sigma> t) \<subseteq> \<sigma> ` (Tfvars t)"
and 
Tmap_cong_id: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Tfvars t. \<sigma> a = a) \<Longrightarrow> Tmap \<sigma> t = t"
and 
Bmap_id[simp]: "Bmap id = id"
and 
Bmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Bmap (\<sigma> o \<tau>) = Bmap \<sigma> o Bmap \<tau>"
and 
small_Bvars: "\<And>xs. wfB xs \<Longrightarrow> small (Bvars xs)" 
and 
Bmap_Bvars: "\<And>xs \<sigma>. ssbij \<sigma> \<Longrightarrow> Bvars (Bmap \<sigma> xs) \<subseteq> \<sigma> ` (Bvars xs)"
and 
Bmap_cong_id: "\<And>xs \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Bvars xs. \<sigma> a = a) \<Longrightarrow> Bmap \<sigma> xs = xs"
begin

(* Being smaller than the number of well-formed binders: *)
definition bsmall :: "'A set \<Rightarrow> bool" where "bsmall X \<equiv> |X| <o |{xs . wfB xs}|"

lemma Tmap_comp': "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) t = Tmap \<sigma> (Tmap \<tau> t)"
using Tmap_comp by fastforce 

lemma image_Tfvars_disj: "ssbij \<sigma> \<Longrightarrow> B \<inter> Tfvars t = {} \<Longrightarrow> image \<sigma> B \<inter> Tfvars (Tmap \<sigma> t) = {}"
using Tmap_Tfvars ssbij_bij by fastforce

lemma Bmap_comp': "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Bmap (\<sigma> o \<tau>) xs = Bmap \<sigma> (Bmap \<tau> xs)"
using Bmap_comp by fastforce 

lemma image_Bvars_disj: "ssbij \<sigma> \<Longrightarrow> B \<inter> Bvars xs = {} \<Longrightarrow> image \<sigma> B \<inter> Bvars (Bmap \<sigma> xs) = {}"
using Bmap_Bvars ssbij_bij by fastforce

(* *)

definition wfBij :: "('A \<Rightarrow> 'A) \<Rightarrow> bool" 
where "wfBij \<sigma> \<equiv> \<forall>xs. wfB xs \<longleftrightarrow> wfB (Bmap \<sigma> xs)"


lemma wfBij_id[simp,intro]: "wfBij id"
unfolding wfBij_def by auto

lemma wfBij_comp[simp]: 
"ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> wfBij \<tau> \<Longrightarrow> wfBij (\<tau> o \<sigma>)"
by (simp add: Bmap_comp' wfBij_def)

lemma wfBij_inv[simp]: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> wfBij (inv \<sigma>)"
by (metis Bmap_comp' Bmap_id id_apply ssbij_inv ssbij_invL wfBij_def)

end (* locale CComponents *)



(* GENERAL VERSIIONS OF THE LOCALES, WIITH wfBij AND closed *)

locale IInduct1 = CComponents dummy Tmap Tfvars Bmap Bvars wfB
for dummy :: 'A 
and Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Bmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bvars :: "'B \<Rightarrow> 'A set"
and wfB 
+
fixes (* The operator that defines the inductive predicate as lfp:  *)
GG :: "('T \<Rightarrow> bool) \<Rightarrow> 'B \<Rightarrow> 'T \<Rightarrow> bool"
(* *)
assumes 
GG_mmono: "\<And>R R' xs t. R \<le> R' \<Longrightarrow> GG R xs t \<Longrightarrow> GG R' xs t"
and 
GG_eequiv: "\<And>\<sigma> R xs t. ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> 
   GG R xs t \<Longrightarrow> GG (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Bmap \<sigma> xs) (Tmap \<sigma> t)"
and 
(* *)
GG_wfB: "\<And>R xs t. GG R xs t \<Longrightarrow> wfB xs"
and 
(* 
extend_wfBij: 
"\<And>A A' B. small A \<Longrightarrow> small B \<Longrightarrow> small A' \<Longrightarrow> A \<inter> A' = {} \<Longrightarrow> closed A
           \<Longrightarrow> \<exists>\<rho>. ssbij \<rho> \<and> wfBij \<rho> \<and> \<rho> ` A \<inter> B = {} \<and> (\<forall>a\<in>A'. \<rho> a = a)" *)
extend_wfBij: 
"\<And>A B. small A \<Longrightarrow> bsmall A \<Longrightarrow> bij_betw \<rho> A B \<Longrightarrow> (\<forall>a\<in>A\<inter>B. \<rho> a = a) \<Longrightarrow> wfBij \<rho> \<Longrightarrow> 
        \<exists>\<rho>'. ssbij \<rho>' \<and> wfBij \<rho>' \<and> (\<forall>a\<in>A. \<rho>' a = \<rho> a)"
begin

lemma GG_mmono2[mono]: "\<And>R R' xs t.  R \<le> R' \<Longrightarrow> GG R xs t \<longrightarrow> GG R' xs t"
  using GG_mmono by blast


inductive II :: "'T \<Rightarrow> bool" where 
GG_II_intro: "GG II xs t \<Longrightarrow> II t"

lemma "II \<equiv> lfp (\<lambda>R t. \<exists>xs. GG R xs t)"
using II_def[simplified] .
 
lemma II_equiv: 
assumes "II t" and \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"
shows "II (Tmap \<sigma> t)"
using assms(1) proof induct 
  case (GG_II_intro xs t)   
  have GG: "GG (\<lambda>t. II (Tmap \<sigma> t)) xs t"
  apply(rule GG_mmono[OF _ GG_II_intro(1)]) using \<sigma> by auto
  have GG: "GG (\<lambda>t. II (Tmap \<sigma> (Tmap (inv \<sigma>) t))) (Bmap \<sigma> xs) (Tmap \<sigma> t)"
  using GG_eequiv[OF \<sigma> GG] .
  have "GG II (Bmap \<sigma> xs) (Tmap \<sigma> t)" 
  apply(rule GG_mmono[OF _ GG])
  using \<sigma> 
  by auto (metis Tmap_comp' Tmap_id id_apply ssbij_inv ssbij_invL) 
  thus ?case by (subst II.simps, auto)
qed

lemma GG_mmono'[mono]: "\<And>R R' xs t.  R \<le> R' \<Longrightarrow> 
 Bvars xs \<inter> Tfvars t = {} \<and> GG R xs t \<longrightarrow> Bvars xs \<inter> Tfvars t = {} \<and> GG R' xs t"
  using GG_mmono by blast

inductive II' :: "'T \<Rightarrow> bool" where 
GG_II'_intro: "Bvars xs \<inter> Tfvars t = {} \<Longrightarrow> GG II' xs t \<Longrightarrow> II' t"

lemma II'_imp_II: "II' t \<Longrightarrow> II t"
apply(induct rule: II'.induct)
by (smt (verit) GG_mmono II.simps predicate1I) 

lemma II'_equiv: 
assumes "II' t" and \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"
shows "II' (Tmap \<sigma> t)"
using assms(1) proof induct
  case (GG_II'_intro xs t)  note B = GG_II'_intro(1)   
  have GG: "GG (\<lambda>t. II' (Tmap \<sigma> t)) xs t" 
  apply(rule GG_mmono[OF _ GG_II'_intro(2)]) using \<sigma> by auto
  have BB: "Bvars (Bmap \<sigma> xs) \<inter> Tfvars (Tmap \<sigma> t) = {}" using image_Tfvars_disj[OF \<sigma>(1) GG_II'_intro(1)] 
  using Bmap_Bvars[OF \<sigma>(1)] by fastforce 
  have GG: "GG (\<lambda>t. II' (Tmap \<sigma> (Tmap (inv \<sigma>) t))) (Bmap \<sigma> xs) (Tmap \<sigma> t)"
  using GG_eequiv[OF \<sigma> GG] .
  have 0: "(\<lambda>t. II' (Tmap \<sigma> (Tmap (inv \<sigma>) t))) = II'"
  unfolding fun_eq_iff  
  by (metis Tmap_comp' Tmap_cong_id \<sigma>(1) id_apply ssbij_comp ssbij_inv ssbij_invL)
  have GG: "GG II' (Bmap \<sigma> xs) (Tmap \<sigma> t)"
  using GG unfolding 0 .
  show ?case using BB GG small_image by (subst II'.simps, auto) 
qed

end (* context IInduct1 *)


locale IInduct = IInduct1 dummy Tmap Tfvars Bmap Bvars wfB GG 
for dummy :: 'A 
and Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Bmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bvars :: "'B \<Rightarrow> 'A set"
and wfB
and GG :: "('T \<Rightarrow> bool) \<Rightarrow> 'B \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
GG_rrefresh: 
"\<And>R xs t. (\<forall>t. R t \<longrightarrow> II t) \<Longrightarrow> 
         (\<forall>\<sigma> t. ssbij \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> GG R xs t \<Longrightarrow> 
         \<exists>ys. Bvars ys \<inter> Tfvars t = {} \<and> GG R ys t"


context IInduct
begin

(* NB: The following could replace GG_refresh in the axiomatization. 
IIt has the advantage that it is weaker, but also two disadvantages:
-- it depends on the "auxiliary" defined predicate II'
-- the dependency on II' seems truly inessential, in that in concrete cases 
all that one needs to use is the equivariance of II'
Later note: in the end, if was useful for getting in inductive information, 
namely strenthening GG_refresh to further assume that R implies II ("\<forall>t. R t \<longrightarrow> II t").  
 *)
lemma GG_refresh_II': 
"\<And>xs t. GG II' xs t \<Longrightarrow> \<exists>ys. Bvars ys \<inter> Tfvars t = {} \<and> GG II' ys t"
using GG_rrefresh II'_equiv by (simp add: II'_imp_II)

lemma II_imp_II': "II t \<Longrightarrow> II' t"
proof(induct rule: II.induct)
  case (GG_II_intro xs t)
  hence GG: "GG II' xs t" by (metis (no_types, lifting) GG_mmono predicate1I)
  from GG_refresh_II'[OF GG]
  obtain ys where 0: "Bvars ys \<inter> Tfvars t = {}" "GG II' ys t" by auto 
  show ?case using II'.intros[OF 0] .
qed

lemma II_eq_II': "II = II'"
apply(rule ext)
subgoal for t
apply(rule iffI)
  subgoal using II_imp_II' by auto 
  subgoal using II'_imp_II by auto . .
 
end (* context IInduct *)


(* The locale with the more restricted rule, in the style of Urban-Berghofer-Norrish: *)
locale IInduct_simple = IInduct1 dummy Tmap Tfvars Bmap Bvars wfB GG 
for dummy :: 'A 
and Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Bmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bvars :: "'B \<Rightarrow> 'A set"
and wfB
and GG :: "('T \<Rightarrow> bool) \<Rightarrow> 'B \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
GG_ffresh: "\<And>R xs t. GG R xs t \<Longrightarrow> Bvars xs \<inter> Tfvars t = {}"


sublocale IInduct_simple < IInduct apply standard
  subgoal using GG_ffresh by blast . 


context IInduct 
begin 
  
(* Barendregt-enhanced (strong) induction. 
NB: we get freshness for t as well, as a bonus (even though the inductive definition of II 
needs not guarantee that -- see again the case of beta-reduction)
 *)


theorem BE_iinduct[consumes 2]: 
(* Parameters: *)
fixes Pfvars :: "'P \<Rightarrow> 'A set"
assumes small_Pfvars: "\<And>p. small (Pfvars p)" 
(* *)
assumes II: "II (t::'T)"
and strong: "\<And> p xs t. Bvars xs \<inter> Pfvars p = {} \<Longrightarrow> Bvars xs \<inter> Tfvars t = {} \<Longrightarrow> 
      GG (\<lambda>t'. II t' \<and> (\<forall>p'. R p' t')) xs t \<Longrightarrow> R p t"
shows "R p t"
proof- 
  {fix \<sigma> assume \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"
   have "R p (Tmap \<sigma> t)"
   using II \<sigma> unfolding II_eq_II' proof(induct arbitrary: \<sigma> p)
     fix xs t \<sigma> p  
     assume vt: "Bvars xs \<inter> Tfvars t = {}" (* this additional vt assumption is what we have gained 
     by transitioning from II to II', whose inductive definition has this freshness side-condition *)
     and GG: "GG (\<lambda>t'. II' t' \<and> (\<forall>\<sigma>'. ssbij \<sigma>' \<longrightarrow> wfBij \<sigma>' \<longrightarrow> (\<forall>p'. R p' (Tmap \<sigma>' t')))) xs t" 
     and \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"

     (* have "II' t"  
       by (metis (no_types, lifting) GG II.simps II_eq_II' IInduct1.GG_mmono IInduct1_axioms predicate1II small_B)
     hence II_T: "II t" using II'_imp_II by auto
     hence "II (Tmap \<sigma> t)" by (simp add: II_equiv \<sigma>(1) \<sigma>(2)) *)

     define xs' where xs': "xs' \<equiv> Bmap \<sigma> xs"


     have "wfB xs" using GG_wfB[OF GG] .
     hence wfB': "wfB xs'"  
     unfolding xs' using \<sigma>(2) wfBij_def by auto 

     have v't: "Bvars xs' \<inter> Tfvars (Tmap \<sigma> t) = {}" 
     using vt unfolding xs'  
     using image_Tfvars_disj \<sigma>  
     by (meson Bmap_Bvars Int_subset_empty1)

     have small_p_t: "small (Pfvars p \<union> Tfvars (Tmap \<sigma> t))"  
       by (simp add: small_Pfvars small_Tfvars small_Un)

     obtain \<rho> where \<rho>: "ssbij \<rho>" "wfBij \<rho>" "\<rho> ` (Bvars xs') \<inter> (Pfvars p \<union> Tfvars (Tmap \<sigma> t)) = {}" 
     "\<forall>a \<in> Tfvars (Tmap \<sigma> t). \<rho> a = a"
     (* using extend_wfBij[of B' "Pfvars p \<union> Tfvars (Tmap \<sigma> t)" "Tfvars (Tmap \<sigma> t)"] 
     using small_Tfvars small_B' small_p_t v't clB' by metis *) sorry
 
     have "\<rho> ` (Bvars xs') \<inter> Pfvars p = {}" 
     and "\<rho> ` (Bvars xs') \<inter> Tfvars (Tmap \<sigma> t) = {}"  
     using \<rho>(1,2,3) by auto
     hence fresh_p: "Bvars (Bmap \<rho> xs') \<inter> Pfvars p = {}" 
     and fresh_t: "Bvars (Bmap \<rho> xs') \<inter> Tfvars (Tmap \<sigma> t) = {}"
     using \<rho>(1) Bmap_Bvars by fastforce+ 

     hence "Tmap \<rho> (Tmap \<sigma> t) = Tmap \<sigma> t" 
     using Tmap_cong_id[OF \<rho>(1,4)] by blast
     hence 0: "Tmap (\<rho> o \<sigma>) t = Tmap \<sigma> t" 
   	 by (simp add: Tmap_comp' \<rho>(1) \<sigma>)

     have \<rho>\<sigma>: "ssbij (\<rho> o \<sigma>)" "wfBij (\<rho> o \<sigma>)" apply (simp add: \<rho>(1) \<sigma> ssbij_comp)
     apply(rule wfBij_comp) using \<sigma> \<rho> by auto

     define \<sigma>'' where \<sigma>'': "\<sigma>'' = \<rho> o \<sigma>"
     have ss_\<sigma>'': "ssbij \<sigma>''" "wfBij \<sigma>''" using \<rho>(1) \<sigma> \<sigma>'' ssbij_comp ssbij_inv apply blast
     using \<rho>\<sigma>(2) \<sigma>'' by blast
   
     have 1[simp]: "\<sigma>'' \<circ> inv (\<rho> o \<sigma>) = id" 
     unfolding \<sigma>'' using \<rho>\<sigma> ssbij_invL by auto  
   
     have "GG (\<lambda>t'. II' t' \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) xs t"  
     apply(rule GG_mmono[OF _ GG]) using ss_\<sigma>'' by auto
     hence GG: "GG (\<lambda>t'. II' (Tmap \<sigma>'' t') \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) xs t" 
     using II'_equiv[OF _ ss_\<sigma>'']  
     by (smt (verit, del_insts) GG_mmono predicate1I) 
     have GG: "GG (\<lambda>t'. II' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')) \<and> 
                      (\<forall>p'. R p' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')))) 
                 (Bmap (\<rho> o \<sigma>) xs) 
                 (Tmap (\<rho> o \<sigma>) t) " 
     using GG_eequiv[OF \<rho>\<sigma> GG] .
     
     have GG: "GG (\<lambda>t'. II' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t') \<and> (\<forall>p'. R p' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t'))) 
                (Bmap \<rho> xs') (Tmap \<sigma> t) "  
     unfolding xs' unfolding image_comp 0[symmetric] Bmap_comp'[symmetric, OF \<rho>(1) \<sigma>(1)] 
     apply(rule GG_mmono[OF _ GG])
     by auto (metis 1 Tmap_comp' Tmap_id \<sigma>'' id_apply ss_\<sigma>''(1) ssbij_inv)+    

     have GG: "GG (\<lambda>t'. II' t' \<and> (\<forall>p'. R p' t')) (Bmap \<rho> xs') (Tmap \<sigma> t)" 
     apply(rule GG_mmono[OF _ GG]) 
     by auto

     show "R p (Tmap \<sigma> t)" 
     using strong[OF fresh_p fresh_t GG[unfolded II_eq_II'[symmetric]]] .
  qed
  }
  from this[of id] show ?thesis 
  by (simp add: ssbij_id)
qed

end (* context IInduct *)



(* VERSIONS OF THE LOCALES WITH SMALL SETS INSTEAD OF BINDER-LIKE ENTITIES, which work in 99% of the cases: *)

locale Components = Small dummy
for dummy :: 'A
+
fixes (* 'T: term-like entities *)
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
assumes  
Tmap_id: "Tmap id = id"
and
Tmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) = Tmap \<sigma> o Tmap \<tau>"
and
small_Tfvars: "\<And>t. small (Tfvars t)"
and 
Tmap_Tfvars: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> Tfvars (Tmap \<sigma> t) \<subseteq> \<sigma> ` (Tfvars t)"
and
Tmap_cong_id: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Tfvars t. \<sigma> a = a) \<Longrightarrow> Tmap \<sigma> t = t"

sublocale Components < CComponents where Tmap = Tmap and Tfvars = Tfvars and 
Bmap = image and Bvars = id and wfB = small apply standard 
using Tmap_id Tmap_comp small_Tfvars Tmap_Tfvars Tmap_cong_id apply auto
by fastforce


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

definition GG where "GG R B t \<equiv> small B \<and> G R B t"

lemma GG_mmono: "R \<le> R' \<Longrightarrow> GG R B t \<Longrightarrow> GG R' B t"
by (simp add: GG_def G_mono)

lemma GG_eequiv: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> 
   GG R B t \<Longrightarrow> GG (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (\<sigma> ` B) (Tmap \<sigma> t)"
using GG_def G_equiv small_image by force

lemma GG_wfB: "GG R B t \<Longrightarrow> small B"
unfolding GG_def by auto

(* In this particular contex, all small bijections are well-formed: *)
lemma ssbij_wfBij: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma>"
unfolding wfBij_def ssbij_def 
using bij_card_of_ordIso ordIso_ordLess_trans ordIso_symmetric small_def by blast

(* and any small set is also bsmall, but it seems we don't have the 
cardinality lemmas yet to prove it (but I don't think we need it): 
lemma small_bsmall: "small A \<Longrightarrow> bsmall A"
unfolding small_def bsmall_def 
sorry
*)

lemma cinfinite_A: "cinfinite |UNIV::'A set|" 
unfolding cinfinite_def 
by (simp add: inf_A)

lemma extend_small: 
assumes "small A" "bij_betw \<rho> A B" "\<forall>a\<in>A\<inter>B. \<rho> a = a"
shows "\<exists>\<rho>'. ssbij \<rho>' \<and> (\<forall>a\<in>A. \<rho>' a = \<rho> a)"
using assms cinfinite_A ex_bij_betw_supp'[of "|UNIV::'A set|" A \<rho> B] 
unfolding eq_on_def small_def ssbij_def by auto

lemma extend_wfBij: 
"small A \<Longrightarrow> bsmall A \<Longrightarrow> bij_betw \<rho> A B \<Longrightarrow> (\<forall>a\<in>A\<inter>B. \<rho> a = a) \<Longrightarrow> wfBij \<rho> \<Longrightarrow> 
     \<exists>\<rho>'. ssbij \<rho>' \<and> wfBij \<rho>' \<and> (\<forall>a\<in>A. \<rho>' a = \<rho> a)"
using extend_small by (metis ssbij_wfBij) 

end (* context Induct1 *)

sublocale Induct1 < IInduct1 where Tmap = Tmap and Tfvars = Tfvars and 
Bmap = image and Bvars = id and wfB = small and GG = GG apply standard 
using GG_mmono GG_eequiv GG_wfB extend_wfBij by auto

context Induct1
begin 


lemma G_mono'[mono]: "\<And>R R' B t. R \<le> R' \<Longrightarrow> small B \<and> G R B t \<longrightarrow> small B \<and> G R' B t"
using G_mono by auto


inductive I :: "'T \<Rightarrow> bool" where 
G_I_intro: "small B \<Longrightarrow> G I B t \<Longrightarrow> I t"

lemma "I \<equiv> lfp (\<lambda>R t. \<exists>B. small B \<and> G R B t)"
using I_def[simplified] .

lemma I_eq_II: "I = II"
apply(intro ext, rule iffI)
  subgoal for t apply (induct rule: I.induct)
    subgoal for B t apply(rule II.intros[of B t])
    unfolding GG_def 
    by (metis (no_types, lifting) G_mono predicate1I) .
  subgoal for t apply (induct rule: II.induct)
    subgoal for B t apply(rule I.intros[of B t])
    unfolding GG_def 
    by (simp,metis (no_types, lifting) G_mono predicate1I) . .
 
lemma I_equiv: 
assumes "I t" and \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"
shows "I (Tmap \<sigma> t)"
using II_equiv I_eq_II assms by auto


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
begin

lemma GG_rrefresh: 
assumes "\<forall>t. R t \<longrightarrow> II t" "\<forall>\<sigma> t. ssbij \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)" "GG R B t"
shows "\<exists>C. C \<inter> Tfvars t = {} \<and> GG R C t"
using G_refresh[OF assms(1)[unfolded I_eq_II[symmetric]]]
using G_refresh[of R B t] unfolding GG_def I_eq_II[symmetric] 
by (metis GG_def assms(2) assms(3) ssbij_wfBij)

end (* context Induct *)

sublocale Induct < IInduct where Tmap = Tmap and Tfvars = Tfvars and 
Bmap = image and Bvars = id and wfB = small and GG = GG apply standard 
by (simp add: GG_rrefresh)


context Induct
begin


thm BE_iinduct 

(* Formulating the theorem in custom form: *)
theorem BE_induct[consumes 2]: 
(* Parameters: *)
fixes Pfvars :: "'P \<Rightarrow> 'A set"
assumes small_Pfvars: "\<And>p. small (Pfvars p)" 
(* *)
assumes I: "I (t::'T)"
and strong: "\<And> p B t. small B \<Longrightarrow> B \<inter> Pfvars p = {} \<Longrightarrow> B \<inter> Tfvars t = {} \<Longrightarrow> 
      G (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) B t \<Longrightarrow> R p t"
shows "R p t"
apply(rule BE_iinduct[of Pfvars _ R p, OF small_Pfvars I[unfolded I_eq_II]])
subgoal for p B t apply(rule strong[of B p t]) 
by (auto simp add: GG_def I_eq_II) .

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
using G_fresh by blast


end 