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

lemma small_UN:
assumes "|I| <o |UNIV::'A set|" and "\<And>i. i \<in> I \<Longrightarrow> small (As i)"
shows "small (\<Union> (As ` I))"
using assms unfolding small_def 
apply(intro ordLess_ordIso_trans[OF regularCard_UNION, of "|UNIV::'A set|"])
using assms inf_A reg_A cinfinite_iff_infinite by auto

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
(* smallness w.r.t. crossing binders: *)
and bsmall :: "'A set \<Rightarrow> bool"
assumes  
TTmap_id[simp]: "Tmap id = id"
and 
TTmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) = Tmap \<sigma> o Tmap \<tau>"
and 
ssmall_Tfvars: "\<And>t. small (Tfvars t)" 
and (* the weaker, inclusion-based version is sufficient (and also for B): *)
TTmap_Tfvars: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> Tfvars (Tmap \<sigma> t) \<subseteq> \<sigma> ` (Tfvars t)"
and 
TTmap_cong_id: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Tfvars t. \<sigma> a = a) \<Longrightarrow> Tmap \<sigma> t = t"
and 
BBmap_id[simp]: "Bmap id = id"
and 
BBmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Bmap (\<sigma> o \<tau>) = Bmap \<sigma> o Bmap \<tau>"
and 
small_Bvars: "\<And>xs. wfB xs \<Longrightarrow> small (Bvars xs)" 
and 
BBmap_Bvars: "\<And>xs \<sigma>. ssbij \<sigma> \<Longrightarrow> Bvars (Bmap \<sigma> xs) \<subseteq> \<sigma> ` (Bvars xs)"
and 
BBmap_cong_id: "\<And>xs \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Bvars xs. \<sigma> a = a) \<Longrightarrow> Bmap \<sigma> xs = xs"
and  
(* bsmallness is subject to properties similar to the ones enjoyed by smallness: *)
bsmall_Bvars: "\<And>xs. wfB xs \<Longrightarrow> bsmall (Bvars xs)" 
and 
bsmall_Un: "bsmall A \<Longrightarrow> bsmall B \<Longrightarrow> bsmall (A \<union> B)"
begin

lemma TTmap_comp': "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) t = Tmap \<sigma> (Tmap \<tau> t)"
using TTmap_comp by fastforce 

lemma image_Tfvars_disj: "ssbij \<sigma> \<Longrightarrow> B \<inter> Tfvars t = {} \<Longrightarrow> image \<sigma> B \<inter> Tfvars (Tmap \<sigma> t) = {}"
using TTmap_Tfvars ssbij_bij by fastforce

lemma BBmap_comp': "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Bmap (\<sigma> o \<tau>) xs = Bmap \<sigma> (Bmap \<tau> xs)"
using BBmap_comp by fastforce 

lemma image_Bvars_disj: "ssbij \<sigma> \<Longrightarrow> B \<inter> Bvars xs = {} \<Longrightarrow> image \<sigma> B \<inter> Bvars (Bmap \<sigma> xs) = {}"
using BBmap_Bvars ssbij_bij by fastforce

(* *)

definition wfBij :: "('A \<Rightarrow> 'A) \<Rightarrow> bool" 
where "wfBij \<sigma> \<equiv> \<forall>xs. wfB xs \<longleftrightarrow> wfB (Bmap \<sigma> xs)"

lemma wfBij_id[simp,intro]: "wfBij id"
unfolding wfBij_def by auto

lemma wfBij_comp[simp]: 
"ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> wfBij \<tau> \<Longrightarrow> wfBij (\<tau> o \<sigma>)"
by (simp add: BBmap_comp' wfBij_def)

lemma wfBij_inv[simp]: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> wfBij (inv \<sigma>)"
by (metis BBmap_comp' BBmap_id id_apply ssbij_inv ssbij_invL wfBij_def)

end (* locale CComponents *)



(* GENERAL VERSIIONS OF THE LOCALES, WIITH wfBij AND closed *)

locale IInduct1 = CComponents dummy Tmap Tfvars Bmap Bvars wfB bsmall
for dummy :: 'A 
and Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Bmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bvars :: "'B \<Rightarrow> 'A set"
and wfB and bsmall
+
fixes (* The operator that defines the inductive predicate as lfp:  *)
GG :: "'B \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
(* *)
assumes 
GG_mmono: "\<And>R R' xs t. R \<le> R' \<Longrightarrow> GG xs R t \<Longrightarrow> GG xs R' t"
and 
GG_eequiv: "\<And>\<sigma> R xs t. ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> 
   GG xs R t \<Longrightarrow> GG  (Bmap \<sigma> xs) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
and 
GG_wfB: "\<And>R xs t. GG xs R t \<Longrightarrow> wfB xs"
and 
extend_to_wfBij: 
"\<And>xs A A'. wfB xs \<Longrightarrow> small A \<Longrightarrow> bsmall A \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> Bvars xs \<inter> A' = {} \<Longrightarrow> 
           \<exists>\<rho>. ssbij \<rho> \<and> wfBij \<rho> \<and> \<rho> ` Bvars xs \<inter> A = {} \<and> id_on A' \<rho>"
begin

lemma GG_mmono2[mono]: "\<And>R R' xs t.  R \<le> R' \<Longrightarrow> GG xs R t \<longrightarrow> GG xs R' t"
  using GG_mmono by blast


inductive II :: "'T \<Rightarrow> bool" where 
GG_II_intro: "GG xs II t \<Longrightarrow> II t"

lemma "II \<equiv> lfp (\<lambda>R t. \<exists>xs. GG xs R t)"
using II_def[simplified] .
 
lemma II_equiv: 
assumes "II t" and \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"
shows "II (Tmap \<sigma> t)"
using assms(1) proof induct 
  case (GG_II_intro xs t)   
  have GG: "GG xs (\<lambda>t. II (Tmap \<sigma> t)) t"
  apply(rule GG_mmono[OF _ GG_II_intro(1)]) using \<sigma> by auto
  have GG: "GG (Bmap \<sigma> xs) (\<lambda>t. II (Tmap \<sigma> (Tmap (inv \<sigma>) t))) (Tmap \<sigma> t)"
  using GG_eequiv[OF \<sigma> GG] .
  have "GG (Bmap \<sigma> xs) II (Tmap \<sigma> t)" 
  apply(rule GG_mmono[OF _ GG])
  using \<sigma> 
  by auto (metis TTmap_comp' TTmap_id id_apply ssbij_inv ssbij_invL) 
  thus ?case by (subst II.simps, auto)
qed

lemma GG_mmono'[mono]: "\<And>R R' xs t.  R \<le> R' \<Longrightarrow> 
 Bvars xs \<inter> Tfvars t = {} \<and> GG xs R t \<longrightarrow> Bvars xs \<inter> Tfvars t = {} \<and> GG xs R' t"
  using GG_mmono by blast

inductive II' :: "'T \<Rightarrow> bool" where 
GG_II'_intro: "Bvars xs \<inter> Tfvars t = {} \<Longrightarrow> GG xs II' t \<Longrightarrow> II' t"

lemma II'_imp_II: "II' t \<Longrightarrow> II t"
apply(induct rule: II'.induct)
by (smt (verit) GG_mmono II.simps predicate1I) 

lemma II'_equiv: 
assumes "II' t" and \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"
shows "II' (Tmap \<sigma> t)"
using assms(1) proof induct
  case (GG_II'_intro xs t)  note B = GG_II'_intro(1)   
  have GG: "GG xs (\<lambda>t. II' (Tmap \<sigma> t)) t" 
  apply(rule GG_mmono[OF _ GG_II'_intro(2)]) using \<sigma> by auto
  have BB: "Bvars (Bmap \<sigma> xs) \<inter> Tfvars (Tmap \<sigma> t) = {}" using image_Tfvars_disj[OF \<sigma>(1) GG_II'_intro(1)] 
  using BBmap_Bvars[OF \<sigma>(1)] by fastforce 
  have GG: "GG (Bmap \<sigma> xs) (\<lambda>t. II' (Tmap \<sigma> (Tmap (inv \<sigma>) t))) (Tmap \<sigma> t)"
  using GG_eequiv[OF \<sigma> GG] .
  have 0: "(\<lambda>t. II' (Tmap \<sigma> (Tmap (inv \<sigma>) t))) = II'"
  unfolding fun_eq_iff  
  by (metis TTmap_comp' TTmap_cong_id \<sigma>(1) id_apply ssbij_comp ssbij_inv ssbij_invL)
  have GG: "GG  (Bmap \<sigma> xs) II'(Tmap \<sigma> t)"
  using GG unfolding 0 .
  show ?case using BB GG small_image by (subst II'.simps, auto) 
qed

end (* context IInduct1 *)


locale IInduct = IInduct1 dummy Tmap Tfvars Bmap Bvars wfB bsmall GG 
for dummy :: 'A 
and Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Bmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bvars :: "'B \<Rightarrow> 'A set"
and wfB and bsmall
and GG :: "'B \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
II_bsmall: "\<And>t. II t \<Longrightarrow> bsmall (Tfvars t)"
and 
GG_rrefresh: 
"\<And>R xs t. (\<forall>t. R t \<longrightarrow> II t) \<Longrightarrow> 
         (\<forall>\<sigma> t. ssbij \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> GG xs R t \<Longrightarrow> 
         \<exists>ys. Bvars ys \<inter> Tfvars t = {} \<and> GG ys R t"



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
"\<And>xs t. GG xs II' t \<Longrightarrow> \<exists>ys. Bvars ys \<inter> Tfvars t = {} \<and> GG ys II' t"
using GG_rrefresh II'_equiv by (simp add: II'_imp_II)

lemma II_imp_II': "II t \<Longrightarrow> II' t"
proof(induct rule: II.induct)
  case (GG_II_intro xs t)
  hence GG: "GG xs II' t" by (metis (no_types, lifting) GG_mmono predicate1I)
  from GG_refresh_II'[OF GG]
  obtain ys where 0: "Bvars ys \<inter> Tfvars t = {}" "GG ys II' t" by auto 
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
locale IInduct_simple = IInduct1 dummy Tmap Tfvars Bmap Bvars wfB bsmall GG 
for dummy :: 'A 
and Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and Bmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bvars :: "'B \<Rightarrow> 'A set"
and wfB and bsmall
and GG :: "'B \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
II_bsmall: "\<And>t. II t \<Longrightarrow> bsmall (Tfvars t)"
and 
GG_ffresh: "\<And>R xs t. GG xs R t \<Longrightarrow> Bvars xs \<inter> Tfvars t = {}"


sublocale IInduct_simple < IInduct apply standard
  using II_bsmall GG_ffresh by blast+


context IInduct 
begin 
  
(* Barendregt-enhanced (strong) induction. 
NB: we get freshness for t as well, as a bonus (even though the inductive definition of II 
needs not guarantee that -- see again the case of beta-reduction)
 *)


lemma extend: 
assumes xs: "wfB xs" and t: "II t" and p: "small (Pfvars p)" "bsmall (Pfvars p)" 
and b: "Bvars xs \<inter> Tfvars t = {}"
shows "\<exists>\<rho>. ssbij \<rho> \<and> wfBij \<rho> \<and> \<rho> ` (Bvars xs) \<inter> (Pfvars p \<union> Tfvars t) = {} \<and> 
           id_on (Tfvars t) \<rho>"
apply(rule extend_to_wfBij)  
  subgoal by fact
  subgoal using p(1) ssmall_Tfvars small_Un by auto
  subgoal by (simp add: II_bsmall bsmall_Un p(2) t)
  subgoal by simp
  subgoal by fact .

theorem BE_iinduct[consumes 2]: 
(* Parameters: *)
fixes Pfvars :: "'P \<Rightarrow> 'A set"
assumes small_Pfvars: "\<And>p. small (Pfvars p) \<and> bsmall (Pfvars p)" 
(* *)
assumes II: "II (t::'T)"
and strong: "\<And> p xs t. Bvars xs \<inter> Pfvars p = {} \<Longrightarrow> Bvars xs \<inter> Tfvars t = {} \<Longrightarrow> 
      GG xs (\<lambda>t'. II t' \<and> (\<forall>p'. R p' t')) t \<Longrightarrow> R p t"
shows "R p t"
proof- 
  {fix \<sigma> assume \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"
   have "R p (Tmap \<sigma> t)"
   using II \<sigma> unfolding II_eq_II' proof(induct arbitrary: \<sigma> p)
     fix xs t \<sigma> p  
     assume vt: "Bvars xs \<inter> Tfvars t = {}" (* this additional vt assumption is what we have gained 
     by transitioning from II to II', whose inductive definition has this freshness side-condition *)
     and GG: "GG xs (\<lambda>t'. II' t' \<and> (\<forall>\<sigma>'. ssbij \<sigma>' \<longrightarrow> wfBij \<sigma>' \<longrightarrow> (\<forall>p'. R p' (Tmap \<sigma>' t')))) t" 
     and \<sigma>: "ssbij \<sigma>" "wfBij \<sigma>"

     have sp: "small (Pfvars p)" "bsmall (Pfvars p)" using small_Pfvars by auto

     have "II' t"  
       by (metis (no_types, lifting) GG II.simps II_eq_II' IInduct1.GG_mmono IInduct1_axioms predicate1I)
     hence II_T: "II t" using II'_imp_II by auto
     hence II_s_t: "II (Tmap \<sigma> t)" by (simp add: II_equiv \<sigma>(1) \<sigma>(2)) 

     define xs' where xs': "xs' \<equiv> Bmap \<sigma> xs"


     have "wfB xs" using GG_wfB[OF GG] .
     hence wfB': "wfB xs'"  
     unfolding xs' using \<sigma>(2) wfBij_def by auto 

     have v't: "Bvars xs' \<inter> Tfvars (Tmap \<sigma> t) = {}" 
     using vt unfolding xs'  
     using image_Tfvars_disj \<sigma>  
     by (meson BBmap_Bvars Int_subset_empty1)

     have small_p_t: "small (Pfvars p \<union> Tfvars (Tmap \<sigma> t))"  
       by (simp add: small_Pfvars ssmall_Tfvars small_Un)

     obtain \<rho> where \<rho>: "ssbij \<rho>" "wfBij \<rho>" "\<rho> ` (Bvars xs') \<inter> (Pfvars p \<union> Tfvars (Tmap \<sigma> t)) = {}" 
     "\<forall>a \<in> Tfvars (Tmap \<sigma> t). \<rho> a = a"
     using extend[OF wfB' II_s_t, of Pfvars, OF sp v't] 
     unfolding id_on_def by metis 
 
     have "\<rho> ` (Bvars xs') \<inter> Pfvars p = {}" 
     and "\<rho> ` (Bvars xs') \<inter> Tfvars (Tmap \<sigma> t) = {}"  
     using \<rho>(1,2,3) by auto
     hence fresh_p: "Bvars (Bmap \<rho> xs') \<inter> Pfvars p = {}" 
     and fresh_t: "Bvars (Bmap \<rho> xs') \<inter> Tfvars (Tmap \<sigma> t) = {}"
     using \<rho>(1) BBmap_Bvars by fastforce+ 

     hence "Tmap \<rho> (Tmap \<sigma> t) = Tmap \<sigma> t" 
     using TTmap_cong_id[OF \<rho>(1,4)] by blast
     hence 0: "Tmap (\<rho> o \<sigma>) t = Tmap \<sigma> t" 
   	 by (simp add: TTmap_comp' \<rho>(1) \<sigma>)

     have \<rho>\<sigma>: "ssbij (\<rho> o \<sigma>)" "wfBij (\<rho> o \<sigma>)" apply (simp add: \<rho>(1) \<sigma> ssbij_comp)
     apply(rule wfBij_comp) using \<sigma> \<rho> by auto

     define \<sigma>'' where \<sigma>'': "\<sigma>'' = \<rho> o \<sigma>"
     have ss_\<sigma>'': "ssbij \<sigma>''" "wfBij \<sigma>''" using \<rho>(1) \<sigma> \<sigma>'' ssbij_comp ssbij_inv apply blast
     using \<rho>\<sigma>(2) \<sigma>'' by blast
   
     have 1[simp]: "\<sigma>'' \<circ> inv (\<rho> o \<sigma>) = id" 
     unfolding \<sigma>'' using \<rho>\<sigma> ssbij_invL by auto  
   
     have "GG xs (\<lambda>t'. II' t' \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) t"  
     apply(rule GG_mmono[OF _ GG]) using ss_\<sigma>'' by auto
     hence GG: "GG xs (\<lambda>t'. II' (Tmap \<sigma>'' t') \<and> (\<forall>p'. R p' (Tmap \<sigma>'' t'))) t" 
     using II'_equiv[OF _ ss_\<sigma>'']  
     by (smt (verit, del_insts) GG_mmono predicate1I) 
     have GG: "GG (Bmap (\<rho> o \<sigma>) xs)
                 (\<lambda>t'. II' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')) \<and> 
                      (\<forall>p'. R p' (Tmap \<sigma>'' (Tmap (inv (\<rho> o \<sigma>)) t')))) 
                 (Tmap (\<rho> o \<sigma>) t) " 
     using GG_eequiv[OF \<rho>\<sigma> GG] .
     
     have GG: "GG (Bmap \<rho> xs') (\<lambda>t'. II' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t') \<and> (\<forall>p'. R p' (Tmap (\<sigma>'' o inv (\<rho> o \<sigma>)) t'))) 
                (Tmap \<sigma> t) "
     unfolding xs' unfolding image_comp 0[symmetric] BBmap_comp'[symmetric, OF \<rho>(1) \<sigma>(1)] 
     apply(rule GG_mmono[OF _ GG])
     by auto (metis 1 TTmap_comp' TTmap_id \<sigma>'' id_apply ss_\<sigma>''(1) ssbij_inv)+    

     have GG: "GG (Bmap \<rho> xs') (\<lambda>t'. II' t' \<and> (\<forall>p'. R p' t')) (Tmap \<sigma> t)" 
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
Bmap = image and Bvars = id and wfB = small and bsmall = "\<lambda>_ . True" apply standard 
using Tmap_id Tmap_comp small_Tfvars Tmap_Tfvars Tmap_cong_id apply auto 
by fastforce


locale Induct1 = Components dummy Tmap Tfvars 
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
+
fixes (* The operator that defines the inductive predicate as lfp:  *)
G :: "'A set \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
assumes 
G_mono: "\<And>R R' B t. R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G B R' t"
and 
G_equiv: "\<And>\<sigma> R B t. ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G (image \<sigma> B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
begin 

definition GG where "GG B R t \<equiv> small B \<and> G B R t"

lemma GGG_mmono: "R \<le> R' \<Longrightarrow> GG B R t \<Longrightarrow> GG B R' t"
by (simp add: GG_def G_mono)

lemma GGG_eequiv: "ssbij \<sigma> \<Longrightarrow>
   GG B R t \<Longrightarrow> GG  (\<sigma> ` B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
using GG_def G_equiv small_image by force

lemma GGG_wfB: "GG B R t \<Longrightarrow> small B"
unfolding GG_def by auto

(* In this particular contex, all small bijections are well-formed: *)
lemma ssbij_wfBij: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma>"
unfolding wfBij_def ssbij_def 
using bij_card_of_ordIso ordIso_ordLess_trans ordIso_symmetric small_def by blast

lemma cinfinite_A: "cinfinite |UNIV::'A set|" 
unfolding cinfinite_def 
by (simp add: inf_A)

lemma extend_small: 
assumes "small A" "bij_betw \<rho> A B" "id_on (A\<inter>B) \<rho>"
shows "\<exists>\<rho>'. ssbij \<rho>' \<and> eq_on A \<rho>' \<rho>"
using assms cinfinite_A ex_bij_betw_supp'[of "|UNIV::'A set|" A \<rho> B] 
unfolding eq_on_def small_def ssbij_def id_on_def eq_on_def by auto

lemma extend_wfBij: 
"small A \<Longrightarrow> bij_betw \<rho> A B \<Longrightarrow> id_on (A\<inter>B) \<rho> \<Longrightarrow> wfBij \<rho> \<Longrightarrow> 
     \<exists>\<rho>'. ssbij \<rho>' \<and> wfBij \<rho>' \<and> eq_on A \<rho>' \<rho>"
using extend_small by (metis ssbij_wfBij) 

lemma eextend_to_wfBij: 
assumes "small B" "small A" "A' \<subseteq> A" "B \<inter> A' = {}"
shows "\<exists>\<rho>. ssbij \<rho> \<and> wfBij \<rho> \<and> \<rho> ` B \<inter> A = {} \<and> id_on A' \<rho>"
proof-
  have "|- (A \<union> B)| =o |UNIV::'A set|"  
  by (metis Compl_eq_Diff_UNIV Un_bound assms(1) assms(2) card_of_Un_diff_infinite inf_A small_def)
  hence "|B| <o |- (A \<union> B)|"  
    using assms(1) ordIso_symmetric ordLess_ordIso_trans small_def by blast
  then obtain f where f: "inj_on f B" "f ` B \<subseteq> - (A \<union> B)" 
    by (meson card_of_ordLeq ordLeq_iff_ordLess_or_ordIso)
  define g where "g \<equiv> \<lambda>a. if a \<in> B then f a else a"
  have g: "inj_on g (B \<union> A')" "g ` (B \<union> A') \<subseteq> - (A \<union> B) \<union> A'" using f 
  unfolding g_def inj_on_def using assms(3,4) by auto
  define C where C: "C = g ` (B \<union> A')"
  have b: "bij_betw g (B \<union> A') C" unfolding C bij_betw_def using g by simp

  have 0: "Cinfinite |UNIV::'A set|" "|B \<union> A'| <o |UNIV::'A set|" "eq_on ((B \<union> A') \<inter> C) g id"
    subgoal by (simp add: cinfinite_A)
    subgoal by (meson assms(1-3) card_of_subset_bound small_Un small_def)
    subgoal using assms(3) f unfolding eq_on_def C g_def by auto .
    
  show ?thesis using ex_bij_betw_supp'[OF 0(1,2) b 0(3)] apply safe
  subgoal for \<rho> apply(rule exI[of _ \<rho>]) using ssbij_wfBij unfolding ssbij_def
  unfolding id_on_def apply auto  
  apply (metis ComplD UnCI eq_on_def f(2) g_def image_subset_iff)
  by (metis Int_emptyD UnCI assms(4) eq_on_def g_def) .
qed

end (* context Induct1 *)

sublocale Induct1 < IInduct1 where Tmap = Tmap and Tfvars = Tfvars and 
Bmap = image and Bvars = id and wfB = small and bsmall = "\<lambda>_. True" and GG = GG apply standard 
using GGG_mmono GGG_eequiv GGG_wfB eextend_to_wfBij by auto

context Induct1
begin 

lemma G_mono'[mono]: "\<And>R R' B t. R \<le> R' \<Longrightarrow> small B \<and> G B R t \<longrightarrow> small B \<and> G B R' t"
using G_mono by auto


inductive I :: "'T \<Rightarrow> bool" where 
G_I_intro: "small B \<Longrightarrow> G B I t \<Longrightarrow> I t"

lemma "I \<equiv> lfp (\<lambda>R t. \<exists>B. small B \<and> G B R t)"
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
assumes "I t" and \<sigma>: "ssbij \<sigma>" 
shows "I (Tmap \<sigma> t)"
using II_equiv I_eq_II assms using ssbij_wfBij by auto


end (* context Induct1 *)
 


locale Induct = Induct1 dummy Tmap Tfvars G  
for dummy :: 'A 
and
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
and 
G :: "'A set \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
G_refresh: 
"\<And>R B t. (\<forall>t. R t \<longrightarrow> I t) \<Longrightarrow> 
         (\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> 
         \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G C R t"
begin

lemma GGG_rrefresh: 
assumes "\<forall>t. R t \<longrightarrow> II t" "\<forall>\<sigma> t. ssbij \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)" "GG B R t"
shows "\<exists>C. C \<inter> Tfvars t = {} \<and> GG C R t"
using G_refresh[OF assms(1)[unfolded I_eq_II[symmetric]]]
using G_refresh[of R B t] unfolding GG_def I_eq_II[symmetric] 
by (metis GG_def assms(2) assms(3) ssbij_wfBij)

end (* context Induct *)

sublocale Induct < IInduct where Tmap = Tmap and Tfvars = Tfvars and 
Bmap = image and Bvars = id and wfB = small and bsmall = "\<lambda>_. True" and GG = GG apply standard 
by (auto simp: GGG_rrefresh)


context Induct
begin


thm BE_iinduct 

(* Formulating the theorem in custom form: *)
theorem strong_induct[consumes 2]: 
(* Parameters: *)
fixes Pfvars :: "'P \<Rightarrow> 'A set"
assumes small_Pfvars: "\<And>p. small (Pfvars p)" 
(* *)
assumes I: "I (t::'T)"
and strong: "\<And> p B t. small B \<Longrightarrow> B \<inter> Pfvars p = {} \<Longrightarrow> B \<inter> Tfvars t = {} \<Longrightarrow> 
      G B (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) t \<Longrightarrow> R p t"
shows "R p t"
apply(rule BE_iinduct[of Pfvars _ R p, OF _ I[unfolded I_eq_II]])
  subgoal using small_Pfvars by auto
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
G :: "'A set \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool" 
+
assumes 
G_fresh: "\<And>R B t. small B \<Longrightarrow> G B R t \<Longrightarrow> B \<inter> Tfvars t = {}"


sublocale Induct_simple < Induct apply standard 
  using G_fresh by blast

print_statement Induct.strong_induct[unfolded
  Induct_def Induct1_def Components_def Small_def
  Induct_axioms_def Induct1_axioms_def Components_axioms_def
  conj_imp_eq_imp_imp, rule_format]

print_statement IInduct.BE_iinduct[unfolded
  IInduct_def IInduct1_def CComponents_def Small_def
  IInduct_axioms_def IInduct1_axioms_def CComponents_axioms_def
  conj_imp_eq_imp_imp, rule_format]


end 