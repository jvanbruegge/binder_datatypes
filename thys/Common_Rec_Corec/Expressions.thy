theory Expressions
  imports "Binders.MRBNF_Recursor" 
begin


(* Prelims: *)
term curry
definition "uncurry f \<equiv> \<lambda>(a,b). f a b" 
lemma uncorry_apply[simp]: "uncurry f (a,b) = f a b"
  unfolding uncurry_def by auto

lemma fst_comp_id[simp]: "fst \<circ> (\<lambda>e. (e, p)) = id" by auto

lemma tri_Un1: "A \<subseteq> B \<union> C \<Longrightarrow> A \<union> B \<subseteq> B \<union> C" by auto
lemma tri_Un3: "A \<union> A' \<union> A'' \<subseteq> B \<union> C \<Longrightarrow> B \<union> A \<union> A' \<union> A'' \<subseteq> B \<union> C" by auto

lemma A_Int_Un_emp: "A \<inter> (B \<union> C) = {} \<longleftrightarrow> A \<inter> B = {} \<and> A \<inter> C = {}" by auto

lemma bij_inv_Un_triv: "bij \<sigma> \<Longrightarrow> \<sigma> ` A \<inter> B = {} \<longleftrightarrow> A \<inter> inv \<sigma> ` B = {}"
  by (metis bij_def empty_is_image image_Int image_inv_f_f surj_imp_inj_inv)

lemma bij_in_inv_Un_triv: "bij \<sigma> \<Longrightarrow> inv \<sigma> a \<in> B \<longleftrightarrow> a \<in> \<sigma> ` B"
  by (metis bij_inv_eq_iff imageE image_eqI)

lemma incl_Un_triv3: "A1 \<union> A2 \<union> A3 \<subseteq> A \<Longrightarrow> A1 \<subseteq> A \<and> A2 \<subseteq> A \<and> A3 \<subseteq> A" by auto

lemma incl_Un3_triv3: "A1 \<subseteq> B1 \<Longrightarrow> A2 \<subseteq> B2 \<union> P \<Longrightarrow> A3 \<subseteq> B3 \<union> P \<Longrightarrow> A1 \<union> A2 \<union> A3 \<subseteq> B1 \<union> B2 \<union> B3 \<union> P" 
by auto

lemma triv_Un4_remove: "A1 \<union> A2 \<union> A3 \<subseteq> B1 \<union> B2 \<union> B3 \<union> P \<Longrightarrow> A1 \<union> A2 \<union> A3 \<union> P \<subseteq> B1 \<union> B2 \<union> B3 \<union> P"
by auto

definition small :: "('a::var \<Rightarrow> 'a) \<Rightarrow> bool" where 
"small \<sigma> \<equiv> countable (supp \<sigma>)" 

declare supp_id[simp,intro] (*: "supp id = {}" unfolding supp_def by auto *)
lemma small_id[simp,intro]: "small id" unfolding small_def by auto
lemma supp_id'[simp,intro]: "supp (\<lambda>a. a) = {}" unfolding supp_def by auto
lemma small_id'[simp,intro]: "small (\<lambda>a. a)" unfolding small_def by auto

thm supp_o
(* lemma supp_o: "supp (\<sigma> o \<tau>) \<subseteq> supp \<sigma> \<union> supp \<tau>" unfolding supp_def by auto *)
lemma small_o[simp]: "small \<sigma> \<Longrightarrow> small \<tau> \<Longrightarrow> small (\<sigma> o \<tau>)" 
unfolding small_def using supp_o by (metis countable_Un_iff countable_subset)

lemma supp_inv[simp]: "bij \<sigma> \<Longrightarrow> small \<sigma> \<Longrightarrow> supp (inv \<sigma>) = supp \<sigma>" 
unfolding supp_def by (metis bij_inv_eq_iff)
lemma small_inv[simp]: "bij \<sigma> \<Longrightarrow> small (inv \<sigma>) \<longleftrightarrow> small \<sigma>" 
unfolding small_def by (metis bij_betw_inv_into inv_inv_eq small_def supp_inv)

(* declare bij_id[intro] *)
lemmas bij_id'[simp,intro]=bij_id[unfolded id_def]
(* declare bij_comp[simp] *)
(* declare bij_imp_bij_inv[simp] *)

lemmas bij_inv_id1 = inv_o_simp2 (* [simp] *) (* : "bij f \<Longrightarrow> f o inv f = id" unfolding fun_eq_iff *)
 (*  by (simp add: bij_def surj_iff) *)
lemmas bij_inv_id2 = inv_o_simp1 
(*[simp]: "bij f \<Longrightarrow> inv f o f = id" unfolding fun_eq_iff 
by (simp add: bij_def surj_iff) *)

(* nominal-like structures: *)
definition nom :: "(('a::var \<Rightarrow> 'a) \<Rightarrow> 'E \<Rightarrow> 'E) \<Rightarrow> ('E \<Rightarrow> 'a set) \<Rightarrow> bool" where 
"nom perm Vrs \<equiv> 
 perm id = id 
 \<and> 
 (\<forall>\<sigma>1 \<sigma>2. small \<sigma>1 \<and> bij \<sigma>1 \<and> small \<sigma>2 \<and> bij \<sigma>2 \<longrightarrow>  
 perm (\<sigma>1 o \<sigma>2) = perm \<sigma>1 o perm \<sigma>2) 
 \<and>
 (\<forall>\<sigma>1 \<sigma>2 e'. 
  small \<sigma>1 \<and> bij \<sigma>1 \<and> small \<sigma>2 \<and> bij \<sigma>2 \<and>  
  (\<forall>a\<in>Vrs e'. \<sigma>1 a = \<sigma>2 a) \<longrightarrow> 
  perm \<sigma>1 e' = perm \<sigma>2 e')"
(* NB: Only if functiins are constrained to be bijective: identity 
 and congruence can be replaced by id_congruence. *)


(*****)

typedecl ('a1, 'a2, 'c1, 'c2) G
consts Gren :: "('a1::var \<Rightarrow> 'a1) \<Rightarrow> ('a2::var \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G"
consts GVrs1 :: "('a1::var, 'a2::var, 'c1, 'c2) G \<Rightarrow> 'a1 set"
consts GVrs2 :: "('a1::var, 'a2::var, 'c1, 'c2) G \<Rightarrow> 'a2 set"
consts Gmap :: "('c1 \<Rightarrow> 'c1') \<Rightarrow> ('c2 \<Rightarrow> 'c2') \<Rightarrow> ('a1::var, 'a2::var, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1', 'c2') G"
consts GSupp1 :: "('a1, 'a2, 'c1, 'c2) G \<Rightarrow> 'c1 set"
consts GSupp2 :: "('a1, 'a2, 'c1, 'c2) G \<Rightarrow> 'c2 set"

axiomatization where 
Gmap_id[simp]: "Gmap id id = id"
and 
Gmap_o: "\<And>f1 g1 f2 g2. Gmap (f1 o g1) (f2 o g2) = Gmap f1 f2 o Gmap g1 g2"
and 
Gren_id[simp]: "Gren id id = id"
and 
Gren_o: "\<And>\<sigma>1 \<tau>1 \<sigma>2 \<tau>2. 
  small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
  small \<tau>1 \<Longrightarrow> bij \<tau>1 \<Longrightarrow> small \<tau>2 \<Longrightarrow> bij \<tau>2 \<Longrightarrow> 
  Gren (\<sigma>1 o \<tau>1) (\<sigma>2 o \<tau>2) = Gren \<sigma>1 \<sigma>2 o Gren \<tau>1 \<tau>2"
and GSupp1_Gmap: "\<And> f1 f2 u. GSupp1 (Gmap f1 f2 u) = f1 ` (GSupp1 u)"
and GSupp2_Gmap: "\<And> f1 f2 u. GSupp2 (Gmap f1 f2 u) = f2 ` (GSupp2 u)"
and GVrs1_Gmap: "\<And> f1 f2 u. GVrs1 (Gmap f1 f2 u) = GVrs1 u"
and GVrs2_Gmap: "\<And> f1 f2 u. GVrs2 (Gmap f1 f2 u) = GVrs2 u"
and Gmap_Gren: "\<And> f1 f2 \<sigma>1 \<sigma>2 u. small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
   Gmap f1 f2 (Gren \<sigma>1 \<sigma>2 u) = Gren \<sigma>1 \<sigma>2 (Gmap f1 f2 u)"
and GVrs1_Gren: "\<And> \<sigma>1 \<sigma>2 u. 
  small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> GVrs1 (Gren \<sigma>1 \<sigma>2 u) = \<sigma>1 ` (GVrs1 u)"
and GVrs2_Gren: "\<And> \<sigma>1 \<sigma>2 u. 
  small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> GVrs2 (Gren \<sigma>1 \<sigma>2 u) = \<sigma>2 ` (GVrs2 u)"
and GSupp1_Gren: "\<And> \<sigma>1 \<sigma>2 u. 
  small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> GSupp1 (Gren \<sigma>1 \<sigma>2 u) = GSupp1 u"
and GSupp2_Gren: "\<And> \<sigma>1 \<sigma>2 u. 
  small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> GSupp2 (Gren \<sigma>1 \<sigma>2 u) = GSupp2 u"
and Gmap_cong: "\<And> f1 f2 g1 g2 u. (\<And>e. e \<in> GSupp1 u \<Longrightarrow> f1 e = g1 e) \<Longrightarrow> 
    (\<And>e. e \<in> GSupp2 u \<Longrightarrow> f2 e = g2 e) \<Longrightarrow> 
    Gmap f1 f2 u = Gmap g1 g2 u"

lemma Gmap_cong_id: 
assumes "\<And>e. e \<in> GSupp1 u \<Longrightarrow> f1 e = e" 
and "\<And>e. e \<in> GSupp2 u \<Longrightarrow> f2 e = e" 
shows "Gmap f1 f2 u = u"
proof-
  have u: "u = Gmap id id u" by simp
  show ?thesis apply(rule sym) apply(subst u)
  apply(rule Gmap_cong) using assms by auto
qed
  
lemma Gmap_comp: "Gmap f1 f2 (Gmap g1 g2 u) = Gmap (f1 o g1) (f2 o g2) u"
  unfolding Gmap_o by simp

lemma Gren_comp: "\<And>\<sigma>1 \<tau>1 \<sigma>2 \<tau>2 u. 
  small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
  small \<tau>1 \<Longrightarrow> bij \<tau>1 \<Longrightarrow> small \<tau>2 \<Longrightarrow> bij \<tau>2 \<Longrightarrow> 
  Gren \<sigma>1 \<sigma>2 (Gren \<tau>1 \<tau>2 u) = Gren (\<sigma>1 o \<tau>1) (\<sigma>2 o \<tau>2) u"
  unfolding Gren_o by simp

lemma Gmap_id'[simp]: "Gmap (\<lambda>x. x) (\<lambda>x. x) = id"
  using Gmap_id unfolding id_def .

lemma snd_single_Gmap: "snd ` GSupp1 u \<subseteq> {p} \<Longrightarrow> snd ` GSupp2 u \<subseteq> {p}
\<Longrightarrow> Gmap (\<lambda>(e,p'). (e,p)) (\<lambda>(e,p'). (e,p)) u = u"
apply(rule Gmap_cong_id) by auto

lemma snd_single_Gmap': 
assumes "snd ` GSupp1 u \<subseteq> {p}" "snd ` GSupp2 u \<subseteq> {p}"
shows "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) (Gmap fst fst u) = u"
apply(rule sym) apply(subst snd_single_Gmap[symmetric, of _ p])
  subgoal by fact subgoal by fact
  subgoal unfolding Gmap_comp o_def  
    by (meson Gmap_cong case_prod_beta) .

(* *)
(* The binding assumption will be: In ('a, 'a, 'a E,'a E) G, 
the first 'a is free, the second 'a binds in the first E. 
*)
typedecl 'a E

consts Ector :: "('a::var, 'a, 'a E,'a E) G \<Rightarrow> 'a E"
consts Eperm :: "('a::var \<Rightarrow> 'a) \<Rightarrow> 'a E \<Rightarrow> 'a E"
consts EVrs :: "('a::var) E \<Rightarrow> 'a set"

axiomatization where Ector_surj_fresh: "\<And>e A. countable A \<Longrightarrow> \<exists>u. Ector u = e \<and> GVrs2 u \<inter> A = {}"
(* Corresponds to ctorPermM *)
and Eperm_Ector: "\<And>\<sigma> u. small \<sigma> \<Longrightarrow> bij \<sigma>  \<Longrightarrow> 
       Eperm \<sigma> (Ector u) = 
       Ector (Gren \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u))"
(* Corresponds to ctorVarsM *)
and EVrs_Ector: "\<And>u. EVrs (Ector u) =
     GVrs1 u \<union>  
     (\<Union> {EVrs e' - GVrs2 u | e' . e' \<in> GSupp1 u}) \<union> 
     (\<Union> {EVrs e' | e' . e' \<in> GSupp2 u})"
and (* Next three correspond to nom *)
Eperm_id[simp]: "Eperm id = id"
and 
Eperm_comp: "\<And>e \<sigma>1 \<sigma>2. small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
    Eperm (\<sigma>1 \<circ> \<sigma>2) e = Eperm \<sigma>1 (Eperm \<sigma>2 e)"
and 
Eperm_cong: 
"\<And>e \<sigma>1 \<sigma>2. small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
 (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma>1 a = \<sigma>2 a) \<Longrightarrow> Eperm \<sigma>1 e = Eperm \<sigma>2 e"
and 
(* 
Ector_eq_imp: 
"\<And>u1 u2. Ector u1 = Ector u2 \<Longrightarrow>
   (\<exists>\<sigma>. small \<sigma> \<and> bij \<sigma> \<and> 
        GVrs1 u1 \<union> 
        (\<Union> {EVrs e | e . e \<in> GSupp1 u1}) \<union> 
        (\<Union> {EVrs e - GVrs2 u1 | e . e \<in> GSupp2 u1}) \<subseteq> supp \<sigma> \<and> 
        u2 = Gren id \<sigma> (Gmap (Eperm \<sigma>) id u1))"
and
*)
Ector_eq_imp_strong: "\<And>A u1 u2. Ector u1 = Ector u2 \<Longrightarrow> countable A \<Longrightarrow> A \<inter> GVrs2 u1 = {} \<Longrightarrow>
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> small \<sigma> \<and>
     id_on ((\<Union> (EVrs ` GSupp1 u1) - GVrs2 u1) \<union> A) \<sigma> \<and> 
     Gren id \<sigma> (Gmap (Eperm \<sigma>) id u1) = u2)"
(* 
Ector_eq_imp: "\<And>u1 u2. Ector u1 = Ector u2 \<Longrightarrow>
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> small \<sigma> \<and>
     id_on ((\<Union> (EVrs ` GSupp1 u1) - GVrs2 u1) \<union> (\<Union> (EVrs ` GSupp2 u1))) \<sigma> \<and> 
     Gren id \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u1) = u2)"
*)


lemma Ector_eqD: "\<And>x y. Ector x = Ector y \<Longrightarrow>
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> small \<sigma> \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> 
      Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  apply(drule Ector_eq_imp_strong) by auto
  (*subgoal for x \<sigma> apply(rule exI[of _ \<sigma>])
apply auto
  subgoal unfolding id_on_def by auto
  subgoal apply(rule arg_cong3[where h = Gren and ?a1.0 = id and ?a2.0 = id and ?b1.0 = \<sigma> and ?b2.0 = \<sigma>])
  apply auto apply(rule Gmap_cong) unfolding id_on_def apply auto  
    by (metis Eperm_comp Eperm_id bij_id eq_id_iff small_id) . .
 *)

lemma Ector_surj: "\<exists>u. Ector u = e"
using Ector_surj_fresh[of "{}"] by auto

lemma Ector_exhaust: "(\<And>u. P (Ector u)) \<Longrightarrow> (\<forall>e. P e)"
by (metis Ector_surj)

lemma Ector_exhaust': "(\<And>u. e = Ector u \<Longrightarrow> P e) \<Longrightarrow> P e"
  by (metis Ector_surj)

lemma Ector_exhaust_fresh: "countable A \<Longrightarrow> (\<And>u. e = Ector u \<Longrightarrow> GVrs2 u \<inter> A = {} \<Longrightarrow> P e) \<Longrightarrow> P e"
  by (metis Ector_surj_fresh)

lemma Eperm_inv_iff: "small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> Eperm (inv \<sigma>) e1 = e \<longleftrightarrow> e1 = Eperm \<sigma> e"
  sorry

lemma nom: "nom Eperm EVrs"
  unfolding nom_def apply safe 
  apply simp
  subgoal using Eperm_comp by fastforce
  subgoal using Eperm_cong by blast .

definition Edtor :: "('a::var) E \<Rightarrow> (('a, 'a, 'a E,'a E) G) set" where 
"Edtor e = {u . Ector u = e}"





(* 
lemma Edtor_EVrs: 
"u\<in>Edtor e \<Longrightarrow> 
 GVrs1 u \<union> 
 (\<Union> {EVrs e | e . e \<in> GSupp1 u}) \<union> 
 (\<Union> {EVrs e - GVrs2 u | e . e \<in> GSupp1 u}) 
 \<subseteq> 
 EVrs e" 
sorry
*)



(****)
(* Parameters *)

typedecl 'a P 
consts Pperm :: "('a::var \<Rightarrow> 'a) \<Rightarrow> 'a P \<Rightarrow> 'a P" 
consts PVrs :: "('a::var) P \<Rightarrow> 'a set"
axiomatization where nomP: "nom Pperm PVrs"
and countable_PVrs: "\<And>p. countable (PVrs p)"
and PVrs_Pperm: "\<And> \<sigma> p u. bij \<sigma> \<Longrightarrow> small \<sigma> \<Longrightarrow> PVrs (Pperm \<sigma> u) = \<sigma> ` PVrs u"

lemma Pperm_id[simp]: "Pperm id = id" 
using nomP[unfolded nom_def] by auto

lemma Pperm_comp: "small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
Pperm \<sigma>1 (Pperm \<sigma>2 p) = Pperm (\<sigma>1 \<circ> \<sigma>2) p"
using nomP[unfolded nom_def] by force

lemma Pperm_cong: 
"small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
 (\<And>a. a \<in> PVrs p \<Longrightarrow> \<sigma>1 a = \<sigma>2 a) \<Longrightarrow> Pperm \<sigma>1 p = Pperm \<sigma>2 p"
  using nomP[unfolded nom_def] by force

lemma countable_PVrs_im: "small \<sigma> \<Longrightarrow> countable (PVrs p \<union> inv \<sigma> ` PVrs p)"
  by (simp add: countable_PVrs)

definition lift :: "(('a::var \<Rightarrow> 'a) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> ('a P\<Rightarrow>'E') \<Rightarrow> ('a P\<Rightarrow>'E'))" where 
"lift perm \<sigma> pe p \<equiv> perm \<sigma> (pe (Pperm (inv \<sigma>) p))"

lemma triv_Eperm_lift: "(\<lambda>e p. e) \<circ> Eperm \<sigma> = lift Eperm \<sigma> o (\<lambda>e p. e)"
  unfolding fun_eq_iff o_def lift_def by simp

definition ctorPermM :: "(('a::var, 'a, 'a P\<Rightarrow>'E','a P\<Rightarrow>'E') G \<Rightarrow> 'a P \<Rightarrow>'E') \<Rightarrow> 
 (('a \<Rightarrow> 'a) \<Rightarrow> 'E' \<Rightarrow> 'E') 
\<Rightarrow> ('a, 'a, 'a P\<Rightarrow>'E','a P\<Rightarrow>'E') G
\<Rightarrow> bool" where 
"ctorPermM ctor perm u \<equiv> 
(\<forall>\<sigma> p. small \<sigma> \<and> bij \<sigma>  \<longrightarrow> 
       perm \<sigma> (ctor u p) = 
       ctor (Gren \<sigma> \<sigma> (Gmap (lift perm \<sigma>) (lift perm \<sigma>) u)) (Pperm \<sigma> p))"

definition ctorVarsM :: "(('a::var, 'a, 'a P\<Rightarrow>'E','a P\<Rightarrow>'E') G \<Rightarrow> 'a P\<Rightarrow>'E') \<Rightarrow> ('E' \<Rightarrow> 'a set) 
\<Rightarrow> ('a, 'a, 'a P\<Rightarrow>'E','a P\<Rightarrow>'E') G
\<Rightarrow> bool" where 
"ctorVarsM ctor Vrs u \<equiv> 
\<forall>p. Vrs (ctor u p) \<subseteq> PVrs p \<union> 
     GVrs1 u \<union> 
     (\<Union> {Vrs (pe p) - GVrs2 u | pe . pe \<in> GSupp1 u}) \<union> 
     (\<Union> {Vrs (pe p) | pe . pe \<in> GSupp2 u})"



end