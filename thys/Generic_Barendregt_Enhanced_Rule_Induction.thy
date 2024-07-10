theory Generic_Barendregt_Enhanced_Rule_Induction
  imports "MRBNF_Recursor"
  keywords "binds" and "binder_inductive" :: thy_goal_defn
begin

declare [[inductive_internals]]

(* General infrastructure: *)
context infinite begin

definition small :: "'a set \<Rightarrow> bool" where 
"small A \<equiv> |A| <o |UNIV::'a set|"(* small/bounded sets *)
definition isPerm :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" (* being a permutation *) where 
"isPerm \<sigma> \<equiv> bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::'a set|"

lemma small_Un: "small A \<Longrightarrow> small B \<Longrightarrow> small (A \<union> B)"
using Un_bound small_def infinite_UNIV by blast

lemma finite_UN_small:
assumes "finite As" and "\<And>A. A \<in> As \<Longrightarrow> small A"
shows "small (\<Union> As)"
using assms apply(induct As)  
using small_Un by (auto simp: infinite_UNIV small_def)

lemma isPerm_bij: "\<And>\<sigma>. isPerm \<sigma> \<Longrightarrow> bij \<sigma>"
unfolding isPerm_def by auto

lemma isPerm_id: "isPerm id" unfolding isPerm_def bij_def  
  by (simp add: supp_id_bound)

lemma isPerm_comp: "isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> isPerm (\<sigma> o \<tau>)"
by (meson infinite_UNIV bij_comp isPerm_def supp_comp_bound)

lemma isPerm_inv: "\<And>\<sigma>. isPerm \<sigma> \<Longrightarrow> isPerm (inv \<sigma>)"
by (simp add: isPerm_def supp_inv_bound)

lemma small_isPerm: 
assumes s: "small A" "small B" "small A'" "A \<inter> A' = {}"
shows "\<exists>\<sigma>. isPerm \<sigma> \<and> \<sigma> ` A \<inter> B = {} \<and> (\<forall>a\<in>A'. \<sigma> a = a)"
proof-
  obtain D where D: "D \<inter> B = {}" "D \<inter> A = {}" "D \<inter> A' = {}" and DA: "|D| =o |A|"
  using exists_subset_compl[of _ A "A' \<union> B"]  
  by (metis Field_card_of Int_Un_emptyI1 Int_Un_emptyI2 Int_commute card_of_Card_order card_of_UNIV 
   cinfinite_def infinite_UNIV ordIso_symmetric s(1-3) small_Un small_def)  

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
    subgoal using bv sv s(1) unfolding isPerm_def small_def 
      by (meson DA card_of_Un_ordLess_infinite card_of_subset_bound infinite_UNIV ordIso_ordLess_trans)
    subgoal using D(1) u(1) by auto
    subgoal using sv D(3) s(4) unfolding supp_def by auto . 
qed

lemma isPerm_invL: "isPerm \<sigma> \<Longrightarrow> \<sigma> o inv \<sigma> = id"
by (meson bij_is_surj isPerm_bij surj_iff)

lemma isPerm_invL': "isPerm \<sigma> \<Longrightarrow> \<sigma> (inv \<sigma> a) = a"
using isPerm_invL pointfree_idE by fastforce

lemma isPerm_invR: "isPerm \<sigma> \<Longrightarrow> inv \<sigma> o \<sigma> = id"
by (meson bij_def inv_o_cancel isPerm_bij)

lemma isPerm_invR': "isPerm \<sigma> \<Longrightarrow> inv \<sigma> (\<sigma> a) = a"
using isPerm_invR pointfree_idE by fastforce

lemma small_empty[simp,intro!]: "small {}"  
  by (simp add: infinite_UNIV small_def)

lemma small_singl[simp,intro!]: "small {x}" 
  by (simp add: infinite_UNIV small_def)

lemma small_two[simp,intro!]: "small {x,y}" 
  by (simp add: infinite_UNIV small_def)

lemma small_three[simp,intro!]: "small {x,y,z}" 
  by (simp add: infinite_UNIV small_def)

lemma small_image: "small B \<Longrightarrow> small (\<sigma> ` B)"
using card_of_image ordLeq_ordLess_trans small_def by blast

lemmas image_comp' = image_comp[symmetric]

end (* context infinite *)


locale CComponents =
  (* 'T: term-like entities, ranged over by t *)
fixes Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
  (* 'B: binder-like entities, ranged over by xs *)
and Bperm :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bsupp :: "'B \<Rightarrow> 'A set"
  (* well-formed binders: *)
and wfB :: "'B \<Rightarrow> bool" 
(* smallness w.r.t. crossing binders: *)
and bsmall :: "'A set \<Rightarrow> bool"
assumes  
TTperm_id[simp]: "Tperm id = id"
and 
TTperm_comp: "\<And>\<sigma> \<tau>. isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Tperm (\<sigma> o \<tau>) = Tperm \<sigma> o Tperm \<tau>"
and 
ssmall_Tsupp: "\<And>t. small (Tsupp t)" 
and (* the weaker, inclusion-based version is sufficient (and also for B): *)
TTperm_Tsupp: "\<And>t \<sigma>. isPerm \<sigma> \<Longrightarrow> Tsupp (Tperm \<sigma> t) \<subseteq> \<sigma> ` (Tsupp t)"
and 
TTperm_cong_id: "\<And>t \<sigma>. isPerm \<sigma> \<Longrightarrow> (\<forall>a\<in>Tsupp t. \<sigma> a = a) \<Longrightarrow> Tperm \<sigma> t = t"
and 
BBperm_id[simp]: "Bperm id = id"
and 
BBperm_comp: "\<And>\<sigma> \<tau>. isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Bperm (\<sigma> o \<tau>) = Bperm \<sigma> o Bperm \<tau>"
and 
small_Bsupp: "\<And>xs. wfB xs \<Longrightarrow> small (Bsupp xs)" 
and 
BBperm_Bsupp: "\<And>xs \<sigma>. isPerm \<sigma> \<Longrightarrow> Bsupp (Bperm \<sigma> xs) \<subseteq> \<sigma> ` (Bsupp xs)"
and 
BBperm_cong_id: "\<And>xs \<sigma>. isPerm \<sigma> \<Longrightarrow> (\<forall>a\<in>Bsupp xs. \<sigma> a = a) \<Longrightarrow> Bperm \<sigma> xs = xs"
and  
(* bsmallness is subject to properties similar to the ones enjoyed by smallness: *)
bsmall_Bsupp: "\<And>xs. wfB xs \<Longrightarrow> bsmall (Bsupp xs)" 
and 
bsmall_Un: "bsmall A \<Longrightarrow> bsmall B \<Longrightarrow> bsmall (A \<union> B)"
begin

lemma TTperm_comp': "isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Tperm (\<sigma> o \<tau>) t = Tperm \<sigma> (Tperm \<tau> t)"
using TTperm_comp by fastforce 

lemma image_Tsupp_disj: "isPerm \<sigma> \<Longrightarrow> B \<inter> Tsupp t = {} \<Longrightarrow> image \<sigma> B \<inter> Tsupp (Tperm \<sigma> t) = {}"
using TTperm_Tsupp isPerm_bij by fastforce

lemma BBperm_comp': "isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Bperm (\<sigma> o \<tau>) xs = Bperm \<sigma> (Bperm \<tau> xs)"
using BBperm_comp by fastforce 

lemma image_Bsupp_disj: "isPerm \<sigma> \<Longrightarrow> B \<inter> Bsupp xs = {} \<Longrightarrow> image \<sigma> B \<inter> Bsupp (Bperm \<sigma> xs) = {}"
using BBperm_Bsupp isPerm_bij by fastforce

(* *)

definition wfBij :: "('A \<Rightarrow> 'A) \<Rightarrow> bool" 
where "wfBij \<sigma> \<equiv> \<forall>xs. wfB xs \<longleftrightarrow> wfB (Bperm \<sigma> xs)"

lemma wfBij_id[simp,intro]: "wfBij id"
unfolding wfBij_def by auto

lemma wfBij_comp[simp]: 
"isPerm \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> wfBij \<tau> \<Longrightarrow> wfBij (\<tau> o \<sigma>)"
by (simp add: BBperm_comp' wfBij_def)

lemma wfBij_inv[simp]: "isPerm \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> wfBij (inv \<sigma>)"
by (metis BBperm_comp' BBperm_id id_apply isPerm_inv isPerm_invL wfBij_def)

end (* locale CComponents *)



(* GENERAL VERSIIONS OF THE LOCALES, WIITH wfBij AND closed *)

locale IInduct1 = CComponents Tperm Tsupp Bperm Bsupp wfB bsmall
for Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
and Bperm :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bsupp :: "'B \<Rightarrow> 'A set"
and wfB and bsmall
+
fixes (* The operator that defines the inductive predicate as lfp:  *)
GG :: "'B \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
(* *)
assumes 
GG_mmono: "\<And>R R' xs t. R \<le> R' \<Longrightarrow> GG xs R t \<Longrightarrow> GG xs R' t"
and 
GG_eequiv: "\<And>\<sigma> R xs t. isPerm \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> 
   GG xs R t \<Longrightarrow> GG  (Bperm \<sigma> xs) (\<lambda>t'. R (Tperm (inv \<sigma>) t')) (Tperm \<sigma> t)"
and 
GG_wfB: "\<And>R xs t. GG xs R t \<Longrightarrow> wfB xs"
and 
extend_to_wfBij: 
"\<And>xs A A'. wfB xs \<Longrightarrow> small A \<Longrightarrow> bsmall A \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> Bsupp xs \<inter> A' = {} \<Longrightarrow> 
           \<exists>\<rho>. isPerm \<rho> \<and> wfBij \<rho> \<and> \<rho> ` Bsupp xs \<inter> A = {} \<and> id_on A' \<rho>"
begin

lemma GG_mmono2[mono]: "\<And>R R' xs t.  R \<le> R' \<Longrightarrow> GG xs R t \<longrightarrow> GG xs R' t"
  using GG_mmono by blast


inductive II :: "'T \<Rightarrow> bool" where 
GG_II_intro: "GG xs II t \<Longrightarrow> II t"

lemma "II \<equiv> lfp (\<lambda>R t. \<exists>xs. GG xs R t)"
using II_def[simplified] .
 
lemma II_equiv: 
assumes "II t" and \<sigma>: "isPerm \<sigma>" "wfBij \<sigma>"
shows "II (Tperm \<sigma> t)"
using assms(1) proof induct 
  case (GG_II_intro xs t)   
  have GG: "GG xs (\<lambda>t. II (Tperm \<sigma> t)) t"
  apply(rule GG_mmono[OF _ GG_II_intro(1)]) using \<sigma> by auto
  have GG: "GG (Bperm \<sigma> xs) (\<lambda>t. II (Tperm \<sigma> (Tperm (inv \<sigma>) t))) (Tperm \<sigma> t)"
  using GG_eequiv[OF \<sigma> GG] .
  have "GG (Bperm \<sigma> xs) II (Tperm \<sigma> t)" 
  apply(rule GG_mmono[OF _ GG])
  using \<sigma> 
  by auto (metis TTperm_comp' TTperm_id id_apply isPerm_inv isPerm_invL) 
  thus ?case by (subst II.simps, auto)
qed

lemma GG_mmono'[mono]: "\<And>R R' xs t.  R \<le> R' \<Longrightarrow> 
 Bsupp xs \<inter> Tsupp t = {} \<and> GG xs R t \<longrightarrow> Bsupp xs \<inter> Tsupp t = {} \<and> GG xs R' t"
  using GG_mmono by blast

inductive II' :: "'T \<Rightarrow> bool" where 
GG_II'_intro: "Bsupp xs \<inter> Tsupp t = {} \<Longrightarrow> GG xs II' t \<Longrightarrow> II' t"

lemma II'_imp_II: "II' t \<Longrightarrow> II t"
apply(induct rule: II'.induct)
by (smt (verit) GG_mmono II.simps predicate1I) 

lemma II'_equiv: 
assumes "II' t" and \<sigma>: "isPerm \<sigma>" "wfBij \<sigma>"
shows "II' (Tperm \<sigma> t)"
using assms(1) proof induct
  case (GG_II'_intro xs t)  note B = GG_II'_intro(1)   
  have GG: "GG xs (\<lambda>t. II' (Tperm \<sigma> t)) t" 
  apply(rule GG_mmono[OF _ GG_II'_intro(2)]) using \<sigma> by auto
  have BB: "Bsupp (Bperm \<sigma> xs) \<inter> Tsupp (Tperm \<sigma> t) = {}" using image_Tsupp_disj[OF \<sigma>(1) GG_II'_intro(1)] 
  using BBperm_Bsupp[OF \<sigma>(1)] by fastforce 
  have GG: "GG (Bperm \<sigma> xs) (\<lambda>t. II' (Tperm \<sigma> (Tperm (inv \<sigma>) t))) (Tperm \<sigma> t)"
  using GG_eequiv[OF \<sigma> GG] .
  have 0: "(\<lambda>t. II' (Tperm \<sigma> (Tperm (inv \<sigma>) t))) = II'"
  unfolding fun_eq_iff  
  by (metis TTperm_comp' TTperm_cong_id \<sigma>(1) id_apply isPerm_comp isPerm_inv isPerm_invL)
  have GG: "GG  (Bperm \<sigma> xs) II'(Tperm \<sigma> t)"
  using GG unfolding 0 .
  show ?case using BB GG small_image by (subst II'.simps, auto) 
qed

end (* context IInduct1 *)


locale IInduct = IInduct1 Tperm Tsupp Bperm Bsupp wfB bsmall GG 
for Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
and Bperm :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bsupp :: "'B \<Rightarrow> 'A set"
and wfB and bsmall
and GG :: "'B \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
II_bsmall: "\<And>t. II t \<Longrightarrow> bsmall (Tsupp t)"
and 
GG_rrefresh: 
"\<And>R xs t. (\<forall>t. R t \<longrightarrow> II t) \<Longrightarrow> 
         (\<forall>\<sigma> t. isPerm \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t)) \<Longrightarrow> GG xs R t \<Longrightarrow> 
         \<exists>ys. Bsupp ys \<inter> Tsupp t = {} \<and> GG ys R t"



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
"\<And>xs t. GG xs II' t \<Longrightarrow> \<exists>ys. Bsupp ys \<inter> Tsupp t = {} \<and> GG ys II' t"
using GG_rrefresh II'_equiv by (simp add: II'_imp_II)

lemma II_imp_II': "II t \<Longrightarrow> II' t"
proof(induct rule: II.induct)
  case (GG_II_intro xs t)
  hence GG: "GG xs II' t" by (metis (no_types, lifting) GG_mmono predicate1I)
  from GG_refresh_II'[OF GG]
  obtain ys where 0: "Bsupp ys \<inter> Tsupp t = {}" "GG ys II' t" by auto 
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
locale IInduct_simple = IInduct1 Tperm Tsupp Bperm Bsupp wfB bsmall GG 
for Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
and Bperm :: "('A \<Rightarrow> 'A) \<Rightarrow> 'B \<Rightarrow> 'B"
and Bsupp :: "'B \<Rightarrow> 'A set"
and wfB and bsmall
and GG :: "'B \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
II_bsmall: "\<And>t. II t \<Longrightarrow> bsmall (Tsupp t)"
and 
GG_ffresh: "\<And>R xs t. GG xs R t \<Longrightarrow> Bsupp xs \<inter> Tsupp t = {}"


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
and b: "Bsupp xs \<inter> Tsupp t = {}"
shows "\<exists>\<rho>. isPerm \<rho> \<and> wfBij \<rho> \<and> \<rho> ` (Bsupp xs) \<inter> (Pfvars p \<union> Tsupp t) = {} \<and> 
           id_on (Tsupp t) \<rho>"
apply(rule extend_to_wfBij)  
  subgoal by fact
  subgoal using p(1) ssmall_Tsupp small_Un by auto
  subgoal by (simp add: II_bsmall bsmall_Un p(2) t)
  subgoal by simp
  subgoal by fact .

theorem BE_iinduct[consumes 2]: 
(* Parameters: *)
fixes Pfvars :: "'P \<Rightarrow> 'A set"
assumes small_Pfvars: "\<And>p. small (Pfvars p) \<and> bsmall (Pfvars p)" 
(* *)
assumes II: "II (t::'T)"
and strong: "\<And> p xs t. Bsupp xs \<inter> Pfvars p = {} \<Longrightarrow> Bsupp xs \<inter> Tsupp t = {} \<Longrightarrow> 
      GG xs (\<lambda>t'. II t' \<and> (\<forall>p'. R p' t')) t \<Longrightarrow> R p t"
shows "R p t"
proof- 
  {fix \<sigma> assume \<sigma>: "isPerm \<sigma>" "wfBij \<sigma>"
   have "R p (Tperm \<sigma> t)"
   using II \<sigma> unfolding II_eq_II' proof(induct arbitrary: \<sigma> p)
     fix xs t \<sigma> p  
     assume vt: "Bsupp xs \<inter> Tsupp t = {}" (* this additional vt assumption is what we have gained 
     by transitioning from II to II', whose inductive definition has this freshness side-condition *)
     and GG: "GG xs (\<lambda>t'. II' t' \<and> (\<forall>\<sigma>'. isPerm \<sigma>' \<longrightarrow> wfBij \<sigma>' \<longrightarrow> (\<forall>p'. R p' (Tperm \<sigma>' t')))) t" 
     and \<sigma>: "isPerm \<sigma>" "wfBij \<sigma>"

     have sp: "small (Pfvars p)" "bsmall (Pfvars p)" using small_Pfvars by auto

     have "II' t"  
       by (metis (no_types, lifting) GG II.simps II_eq_II' IInduct1.GG_mmono IInduct1_axioms predicate1I)
     hence II_T: "II t" using II'_imp_II by auto
     hence II_s_t: "II (Tperm \<sigma> t)" by (simp add: II_equiv \<sigma>(1) \<sigma>(2)) 

     define xs' where xs': "xs' \<equiv> Bperm \<sigma> xs"


     have "wfB xs" using GG_wfB[OF GG] .
     hence wfB': "wfB xs'"  
     unfolding xs' using \<sigma>(2) wfBij_def by auto 

     have v't: "Bsupp xs' \<inter> Tsupp (Tperm \<sigma> t) = {}" 
     using vt unfolding xs'  
     using image_Tsupp_disj \<sigma>  
     by (meson BBperm_Bsupp Int_subset_empty1)

     have small_p_t: "small (Pfvars p \<union> Tsupp (Tperm \<sigma> t))"  
       by (simp add: small_Pfvars ssmall_Tsupp small_Un)

     obtain \<rho> where \<rho>: "isPerm \<rho>" "wfBij \<rho>" "\<rho> ` (Bsupp xs') \<inter> (Pfvars p \<union> Tsupp (Tperm \<sigma> t)) = {}" 
     "\<forall>a \<in> Tsupp (Tperm \<sigma> t). \<rho> a = a"
     using extend[OF wfB' II_s_t, of Pfvars, OF sp v't] 
     unfolding id_on_def by metis 
 
     have "\<rho> ` (Bsupp xs') \<inter> Pfvars p = {}" 
     and "\<rho> ` (Bsupp xs') \<inter> Tsupp (Tperm \<sigma> t) = {}"  
     using \<rho>(1,2,3) by auto
     hence fresh_p: "Bsupp (Bperm \<rho> xs') \<inter> Pfvars p = {}" 
     and fresh_t: "Bsupp (Bperm \<rho> xs') \<inter> Tsupp (Tperm \<sigma> t) = {}"
     using \<rho>(1) BBperm_Bsupp by fastforce+ 

     hence "Tperm \<rho> (Tperm \<sigma> t) = Tperm \<sigma> t" 
     using TTperm_cong_id[OF \<rho>(1,4)] by blast
     hence 0: "Tperm (\<rho> o \<sigma>) t = Tperm \<sigma> t" 
   	 by (simp add: TTperm_comp' \<rho>(1) \<sigma>)

     have \<rho>\<sigma>: "isPerm (\<rho> o \<sigma>)" "wfBij (\<rho> o \<sigma>)" apply (simp add: \<rho>(1) \<sigma> isPerm_comp)
     apply(rule wfBij_comp) using \<sigma> \<rho> by auto

     define \<sigma>'' where \<sigma>'': "\<sigma>'' = \<rho> o \<sigma>"
     have ss_\<sigma>'': "isPerm \<sigma>''" "wfBij \<sigma>''" using \<rho>(1) \<sigma> \<sigma>'' isPerm_comp isPerm_inv apply blast
     using \<rho>\<sigma>(2) \<sigma>'' by blast
   
     have 1[simp]: "\<sigma>'' \<circ> inv (\<rho> o \<sigma>) = id" 
     unfolding \<sigma>'' using \<rho>\<sigma> isPerm_invL by auto  
   
     have "GG xs (\<lambda>t'. II' t' \<and> (\<forall>p'. R p' (Tperm \<sigma>'' t'))) t"  
     apply(rule GG_mmono[OF _ GG]) using ss_\<sigma>'' by auto
     hence GG: "GG xs (\<lambda>t'. II' (Tperm \<sigma>'' t') \<and> (\<forall>p'. R p' (Tperm \<sigma>'' t'))) t" 
     using II'_equiv[OF _ ss_\<sigma>'']  
     by (smt (verit, del_insts) GG_mmono predicate1I) 
     have GG: "GG (Bperm (\<rho> o \<sigma>) xs)
                 (\<lambda>t'. II' (Tperm \<sigma>'' (Tperm (inv (\<rho> o \<sigma>)) t')) \<and> 
                      (\<forall>p'. R p' (Tperm \<sigma>'' (Tperm (inv (\<rho> o \<sigma>)) t')))) 
                 (Tperm (\<rho> o \<sigma>) t) " 
     using GG_eequiv[OF \<rho>\<sigma> GG] .
     
     have GG: "GG (Bperm \<rho> xs') (\<lambda>t'. II' (Tperm (\<sigma>'' o inv (\<rho> o \<sigma>)) t') \<and> (\<forall>p'. R p' (Tperm (\<sigma>'' o inv (\<rho> o \<sigma>)) t'))) 
                (Tperm \<sigma> t) "
     unfolding xs' unfolding image_comp 0[symmetric] BBperm_comp'[symmetric, OF \<rho>(1) \<sigma>(1)] 
     apply(rule GG_mmono[OF _ GG])
     by auto (metis 1 TTperm_comp' TTperm_id \<sigma>'' id_apply ss_\<sigma>''(1) isPerm_inv)+    

     have GG: "GG (Bperm \<rho> xs') (\<lambda>t'. II' t' \<and> (\<forall>p'. R p' t')) (Tperm \<sigma> t)" 
     apply(rule GG_mmono[OF _ GG]) 
     by auto

     show "R p (Tperm \<sigma> t)" 
     using strong[OF fresh_p fresh_t GG[unfolded II_eq_II'[symmetric]]] .
  qed
  }
  from this[of id] show ?thesis 
  by (simp add: isPerm_id)
qed

end (* context IInduct *)



(* VERSIONS OF THE LOCALES WITH SMALL SETS INSTEAD OF BINDER-LIKE ENTITIES, which work in 99% of the cases: *)

locale Components =
fixes (* 'T: term-like entities *)
Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
assumes  
Tperm_id: "Tperm id = id"
and
Tperm_comp: "\<And>\<sigma> \<tau>. isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Tperm (\<sigma> o \<tau>) = Tperm \<sigma> o Tperm \<tau>"
and
small_Tsupp: "\<And>t. small (Tsupp t)"
and 
Tperm_Tsupp: "\<And>t \<sigma>. isPerm \<sigma> \<Longrightarrow> Tsupp (Tperm \<sigma> t) \<subseteq> \<sigma> ` (Tsupp t)"
and
Tperm_cong_id: "\<And>t \<sigma>. isPerm \<sigma> \<Longrightarrow> (\<forall>a\<in>Tsupp t. \<sigma> a = a) \<Longrightarrow> Tperm \<sigma> t = t"

sublocale Components < CComponents where Tperm = Tperm and Tsupp = Tsupp and 
Bperm = image and Bsupp = id and wfB = small and bsmall = "\<lambda>_ . True" apply standard 
using Tperm_id Tperm_comp small_Tsupp Tperm_Tsupp Tperm_cong_id apply auto 
by fastforce


locale Induct1 = Components Tperm Tsupp 
for Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
+
fixes (* The operator that defines the inductive predicate as lfp:  *)
G :: "'A set \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
assumes 
G_mono: "\<And>R R' B t. R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G B R' t"
and 
G_equiv: "\<And>\<sigma> R B t. isPerm \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G (image \<sigma> B) (\<lambda>t'. R (Tperm (inv \<sigma>) t')) (Tperm \<sigma> t)"
begin 

definition GG where "GG B R t \<equiv> small B \<and> G B R t"

lemma GGG_mmono: "R \<le> R' \<Longrightarrow> GG B R t \<Longrightarrow> GG B R' t"
by (simp add: GG_def G_mono)

lemma GGG_eequiv: "isPerm \<sigma> \<Longrightarrow>
   GG B R t \<Longrightarrow> GG  (\<sigma> ` B) (\<lambda>t'. R (Tperm (inv \<sigma>) t')) (Tperm \<sigma> t)"
using GG_def G_equiv small_image by force

lemma GGG_wfB: "GG B R t \<Longrightarrow> small B"
unfolding GG_def by auto

(* In this particular contex, all small bijections are well-formed: *)
lemma isPerm_wfBij: "isPerm \<sigma> \<Longrightarrow> wfBij \<sigma>"
unfolding wfBij_def isPerm_def 
using bij_card_of_ordIso ordIso_ordLess_trans ordIso_symmetric small_def by blast

lemma cinfinite_A: "cinfinite |UNIV::'A set|" 
unfolding cinfinite_def 
by (simp add: infinite_UNIV)

lemma extend_small: 
assumes "small (A :: 'A set)" "bij_betw \<rho> A B" "id_on (A\<inter>B) \<rho>"
shows "\<exists>\<rho>'. isPerm \<rho>' \<and> eq_on A \<rho>' \<rho>"
using assms cinfinite_A ex_bij_betw_supp'[of "|UNIV::'A set|" A \<rho> B] 
unfolding eq_on_def small_def isPerm_def id_on_def eq_on_def by auto

lemma extend_wfBij: 
"small A \<Longrightarrow> bij_betw \<rho> A B \<Longrightarrow> id_on (A\<inter>B) \<rho> \<Longrightarrow> wfBij \<rho> \<Longrightarrow> 
     \<exists>\<rho>'. isPerm \<rho>' \<and> wfBij \<rho>' \<and> eq_on A \<rho>' \<rho>"
using extend_small by (metis isPerm_wfBij) 

lemma eextend_to_wfBij: 
assumes "small B" "small A" "A' \<subseteq> A" "B \<inter> A' = {}"
shows "\<exists>\<rho>. isPerm \<rho> \<and> wfBij \<rho> \<and> \<rho> ` B \<inter> A = {} \<and> id_on A' \<rho>"
proof-
  have "|- (A \<union> B)| =o |UNIV::'A set|"  
  by (metis Compl_eq_Diff_UNIV Un_bound assms(1) assms(2) card_of_Un_diff_infinite infinite_UNIV small_def)
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
  subgoal for \<rho> apply(rule exI[of _ \<rho>]) using isPerm_wfBij unfolding isPerm_def
  unfolding id_on_def apply auto  
  apply (metis ComplD UnCI eq_on_def f(2) g_def image_subset_iff)
  by (metis Int_emptyD UnCI assms(4) eq_on_def g_def) .
qed

end (* context Induct1 *)

sublocale Induct1 < IInduct1 where Tperm = Tperm and Tsupp = Tsupp and 
Bperm = image and Bsupp = id and wfB = small and bsmall = "\<lambda>_. True" and GG = GG apply standard 
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
assumes "I t" and \<sigma>: "isPerm \<sigma>" 
shows "I (Tperm \<sigma> t)"
using II_equiv I_eq_II assms using isPerm_wfBij by auto


end (* context Induct1 *)
 


locale Induct = Induct1 Tperm Tsupp G  
for Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
and 
G :: "'A set \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool"
+
assumes 
G_refresh: 
"\<And>R B t. (\<forall>t. R t \<longrightarrow> I t) \<Longrightarrow> 
         (\<forall>\<sigma> t. isPerm \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> 
         \<exists>C. small C \<and> C \<inter> Tsupp t = {} \<and> G C R t"
begin

lemma GGG_rrefresh: 
assumes "\<forall>t. R t \<longrightarrow> II t" "\<forall>\<sigma> t. isPerm \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t)" "GG B R t"
shows "\<exists>C. C \<inter> Tsupp t = {} \<and> GG C R t"
using G_refresh[OF assms(1)[unfolded I_eq_II[symmetric]]]
using G_refresh[of R B t] unfolding GG_def I_eq_II[symmetric] 
by (metis GG_def assms(2) assms(3) isPerm_wfBij)

end (* context Induct *)

sublocale Induct < IInduct where Tperm = Tperm and Tsupp = Tsupp and 
Bperm = image and Bsupp = id and wfB = small and bsmall = "\<lambda>_. True" and GG = GG apply standard 
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
and strong: "\<And> p B t. small B \<Longrightarrow> B \<inter> Pfvars p = {} \<Longrightarrow> B \<inter> Tsupp t = {} \<Longrightarrow> 
      G B (\<lambda>t'. I t' \<and> (\<forall>p'. R p' t')) t \<Longrightarrow> R p t"
shows "R p t"
apply(rule BE_iinduct[of Pfvars _ R p, OF _ I[unfolded I_eq_II]])
  subgoal using small_Pfvars by auto
  subgoal for p B t apply(rule strong[of B p t]) 
  by (auto simp add: GG_def I_eq_II) .

end (* context Induct *)

(* The locale with the more restricted rule, in the style of Urban-Berghofer-Norrish: *)
locale Induct_simple = Induct1 Tperm Tsupp G 
for Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
and 
G :: "'A set \<Rightarrow> ('T \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> bool" 
+
assumes 
G_fresh: "\<And>R B t. small B \<Longrightarrow> G B R t \<Longrightarrow> B \<inter> Tsupp t = {}"


sublocale Induct_simple < Induct apply standard 
  using G_fresh by blast

print_statement Induct.strong_induct[unfolded
  Induct_def Induct1_def Components_def
  Induct_axioms_def Induct1_axioms_def
  conj_imp_eq_imp_imp, rule_format]

print_statement IInduct.BE_iinduct[unfolded
  IInduct_def IInduct1_def CComponents_def
  IInduct_axioms_def IInduct1_axioms_def
  conj_imp_eq_imp_imp, rule_format]

ML_file \<open>../Tools/binder_inductive.ML\<close>

end 