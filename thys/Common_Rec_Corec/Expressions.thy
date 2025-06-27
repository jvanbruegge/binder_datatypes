theory Expressions
  imports "HOL-Library.Countable_Set_Type"
begin

(* Prelims: *)

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

(* For now just grabbed this: *)

typedef var = "{x::nat set. x \<in> Field (cardSuc natLeq)}"
 by simp (metis Field_cardSuc_not_empty Field_natLeq all_not_in_conv natLeq_card_order)

lemma bij_betw_Rep_var: "bij_betw Rep_var (UNIV::var set) (Field (cardSuc natLeq))"
by (smt (verit, best) Abs_var_inverse Rep_var Rep_var_inject UNIV_I bij_betwI' mem_Collect_eq)


lemma infinite_var: "infinite (UNIV::var set)"
  using Field_natLeq bij_betw_Rep_var bij_betw_finite natLeq_Card_order
  by (metis cardSuc_finite infinite_UNIV_char_0) 

lemma countable_exists_countable_var:
assumes "countable (A::var set)"
shows "\<exists>B. B \<inter> A = {} \<and> infinite B"
  apply(rule exI[of _ "-A"]) apply simp sorry
(* 
by simp (metis Compl_eq_Diff_UNIV assms card_of_Well_order countable_card_var
not_ordLeq_iff_ordLess ordLeq_iff_ordLess_or_ordIso uncountable_infinite uncountable_minus_countable)
*)

lemma countable_exists_finite_var:
assumes "countable (A::var set)"
shows "\<exists>B. B \<inter> A = {} \<and> finite B \<and> card B = n"
proof-
  obtain B' where B': "B' \<inter> A = {}" and iB': "infinite B'"
  using countable_exists_countable_var[OF assms] by auto
  obtain B where "B \<subseteq> B' \<and> finite B \<and> card B = n"
  using iB' by (meson infinite_arbitrarily_large)
  thus ?thesis using B' by auto
qed

lemma countable_exists_list_var:
assumes "countable (A::var set)"
shows "\<exists>xs. set xs \<inter> A = {} \<and> distinct xs \<and> length xs = n"
by (metis assms countable_exists_finite_var distinct_remdups finite_list length_remdups_card_conv set_remdups)

lemma exists_var:
assumes "countable (X::var set)"
shows "\<exists>x. x \<notin> X"
by (metis Int_absorb assms countable_exists_countable_var disjoint_iff finite.emptyI)

lemma finite_exists_var:
assumes "finite X"
shows "\<exists> x::var. x \<notin> X"
by (simp add: assms ex_new_if_finite infinite_var)


(* *)

definition sw :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" where
"sw x y z \<equiv> if x = y then z else if x = z then y else x"

lemma sw_eqL[simp,intro!]: "\<And> x y z. sw x x y = y"
and sw_eqR[simp,intro!]: "\<And> x y z. sw x y x = y"
and sw_diff[simp]: "\<And> x y z. x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> sw x y z = x"
  unfolding sw_def by auto

lemma sw_sym: "sw x y z = sw x z y"
and sw_id[simp]: "sw x y y = x"
and sw_sw: "sw (sw x y z) y1 z1 = sw (sw x y1 z1) (sw y y1 z1) (sw z y1 z1)"
and sw_invol[simp]: "sw (sw x y z) y z = x"
  unfolding sw_def by auto

lemma sw_invol2: "sw (sw x y z) z y = x"
  by (simp add: sw_sym)

lemma sw_inj[iff]: "sw x z1 z2 = sw y z1 z2 \<longleftrightarrow> x = y"
  unfolding sw_def by auto

lemma sw_surj: "\<exists>y. x = sw y z1 z2"
  by (metis sw_invol)

(* *)

definition supp :: "(var \<Rightarrow> var) \<Rightarrow> var set" where 
"supp \<sigma> = {a . \<sigma> a \<noteq> a}"

definition small :: "(var \<Rightarrow> var) \<Rightarrow> bool" where 
"small \<sigma> \<equiv> countable (supp \<sigma>)" 

lemma supp_id[simp,intro]: "supp id = {}" unfolding supp_def by auto
lemma small_id[simp,intro]: "small id" unfolding small_def by auto
lemma supp_id'[simp,intro]: "supp (\<lambda>a. a) = {}" unfolding supp_def by auto
lemma small_id'[simp,intro]: "small (\<lambda>a. a)" unfolding small_def by auto

lemma supp_o: "supp (\<sigma> o \<tau>) \<subseteq> supp \<sigma> \<union> supp \<tau>" unfolding supp_def by auto
lemma small_o[simp]: "small \<sigma> \<Longrightarrow> small \<tau> \<Longrightarrow> small (\<sigma> o \<tau>)" 
unfolding small_def using supp_o by (metis countable_Un_iff countable_subset)

lemma supp_inv[simp]: "bij \<sigma> \<Longrightarrow> small \<sigma> \<Longrightarrow> supp (inv \<sigma>) = supp \<sigma>" 
unfolding supp_def by (metis bij_inv_eq_iff)
lemma small_inv[simp]: "bij \<sigma> \<Longrightarrow> small (inv \<sigma>) \<longleftrightarrow> small \<sigma>" 
unfolding small_def by (metis bij_betw_inv_into inv_inv_eq small_def supp_inv)

declare bij_id[intro]
lemmas bij_id'[simp,intro]=bij_id[unfolded id_def]
declare bij_comp[simp]
declare bij_imp_bij_inv[simp]
find_theorems bij "_ o inv _"
lemma bij_inv_id1[simp]: "bij f \<Longrightarrow> f o inv f = id" unfolding fun_eq_iff 
  by (simp add: bij_def surj_iff)
lemma bij_inv_id2[simp]: "bij f \<Longrightarrow> inv f o f = id" unfolding fun_eq_iff 
by (simp add: bij_def surj_iff)

(* nominal-like structures: *)
definition nom :: "((var \<Rightarrow> var) \<Rightarrow> 'E \<Rightarrow> 'E) \<Rightarrow> ('E \<Rightarrow> var set) \<Rightarrow> bool" where 
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

typedecl ('x1, 'x2) G
consts Gren :: "(var \<Rightarrow> var) \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> ('x1, 'x2) G \<Rightarrow> ('x1, 'x2) G"
consts GVrs1 :: "('x1, 'x2) G \<Rightarrow> var set"
consts GVrs2 :: "('x1, 'x2) G \<Rightarrow> var set"
consts Gmap :: "('x1 \<Rightarrow> 'x1') \<Rightarrow> ('x2 \<Rightarrow> 'x2') \<Rightarrow> ('x1, 'x2) G \<Rightarrow> ('x1', 'x2') G"
consts GSupp1 :: "('x1, 'x2) G \<Rightarrow> 'x1 set"
consts GSupp2 :: "('x1, 'x2) G \<Rightarrow> 'x2 set"

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
typedecl E

consts Ector :: "(E,E) G \<Rightarrow> E"
consts Eperm :: "(var \<Rightarrow> var) \<Rightarrow> E \<Rightarrow> E"
consts EVrs :: "E \<Rightarrow> var set"

axiomatization where Ector_surj_fresh: "\<And>e A. countable A \<Longrightarrow> \<exists>u. Ector u = e \<and> GVrs2 u \<inter> A = {}"
(* Corresponds to ctorPermM *)
and Eperm_Ector: "\<And>\<sigma> u. small \<sigma> \<Longrightarrow> bij \<sigma>  \<Longrightarrow> 
       Eperm \<sigma> (Ector u) = 
       Ector (Gren \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u))"
(* Corresponds to ctorVarsM *)
and EVrs_Ector: "\<And>u. EVrs (Ector u) =
     GVrs1 u \<union> 
     (\<Union> {EVrs e' | e' . e' \<in> GSupp1 u}) \<union> 
     (\<Union> {EVrs e' - GVrs2 u | e' . e' \<in> GSupp1 u})"
and (* Next three correspond to nom *)
Eperm_id[simp]: "Eperm id = id"
and 
Eperm_comp: "small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
    Eperm (\<sigma>1 \<circ> \<sigma>2) e = Eperm \<sigma>1 (Eperm \<sigma>2 p)"
and 
Eperm_cong: 
"small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
 (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma>1 a = \<sigma>2 a) \<Longrightarrow> Eperm \<sigma>1 e = Eperm \<sigma>2 e"
and 
Ector_eq_imp: 
"\<And>u1 u2. Ector u1 = Ector u2 \<Longrightarrow>
   (\<exists>\<sigma>. small \<sigma> \<and> bij \<sigma> \<and> 
        supp \<sigma> \<subseteq> GVrs1 u1 \<union> 
                 (\<Union> {EVrs e | e . e \<in> GSupp1 u1}) \<union> 
                 (\<Union> {EVrs e - GVrs2 u1 | e . e \<in> GSupp1 u1}) \<and> 
        u2 = Gren id \<sigma> u1)"


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
  subgoal using Eperm_comp by auto 
  subgoal using Eperm_cong by blast .

definition Edtor :: "E \<Rightarrow> ((E,E) G) set" where 
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

typedecl P 
consts Pperm :: "(var \<Rightarrow> var) \<Rightarrow> P \<Rightarrow> P" 
consts PVrs :: "P \<Rightarrow> var set"
axiomatization where nomP: "nom Pperm PVrs"
and countable_PVrs: "\<And>p. countable (PVrs p)"
and PVrs_Pperm: "\<And> \<sigma> p. bij \<sigma> \<Longrightarrow> small \<sigma> \<Longrightarrow> PVrs (Pperm \<sigma> u) = \<sigma> ` PVrs u"

lemma Pperm_id[simp]: "Pperm id = id" 
using nomP[unfolded nom_def] by auto

lemma Pperm_comp: "small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
Pperm \<sigma>1 (Pperm \<sigma>2 p) = Pperm (\<sigma>1 \<circ> \<sigma>2) p"
using nomP[unfolded nom_def] by auto

lemma Pperm_cong: 
"small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
 (\<And>a. a \<in> PVrs p \<Longrightarrow> \<sigma>1 a = \<sigma>2 a) \<Longrightarrow> Pperm \<sigma>1 p = Pperm \<sigma>2 p"
  using nomP[unfolded nom_def] by auto

lemma countable_PVrs_im: "small \<sigma> \<Longrightarrow> countable (PVrs p \<union> inv \<sigma> ` PVrs p)"
  by (simp add: countable_PVrs)

definition lift :: "((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> (P\<Rightarrow>'E') \<Rightarrow> (P=>'E'))" where 
"lift perm \<sigma> pe p \<equiv> perm \<sigma> (pe (Pperm (inv \<sigma>) p))"

lemma triv_Eperm_lift: "(\<lambda>e p. e) \<circ> Eperm \<sigma> = lift Eperm \<sigma> o (\<lambda>e p. e)"
  unfolding fun_eq_iff o_def lift_def by simp

definition ctorPermM :: "((P\<Rightarrow>'E',P\<Rightarrow>'E') G \<Rightarrow> P \<Rightarrow>'E') \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') 
\<Rightarrow> (P\<Rightarrow>'E',P\<Rightarrow>'E') G
\<Rightarrow> bool" where 
"ctorPermM ctor perm u \<equiv> 
(\<forall>\<sigma> p. small \<sigma> \<and> bij \<sigma>  \<longrightarrow> 
       perm \<sigma> (ctor u p) = 
       ctor (Gren \<sigma> \<sigma> (Gmap (lift perm \<sigma>) (lift perm \<sigma>) u)) (Pperm \<sigma> p))"

definition ctorVarsM :: "((P\<Rightarrow>'E',P\<Rightarrow>'E') G \<Rightarrow> P\<Rightarrow>'E') \<Rightarrow> ('E' \<Rightarrow> var set) 
\<Rightarrow> (P\<Rightarrow>'E',P\<Rightarrow>'E') G
\<Rightarrow> bool" where 
"ctorVarsM ctor Vrs u \<equiv> 
\<forall>p. Vrs (ctor u p) \<subseteq> PVrs p \<union> 
     GVrs1 u \<union> 
     (\<Union> {Vrs (pe p) | pe . pe \<in> GSupp1 u}) \<union> 
     (\<Union> {Vrs (pe p) - GVrs2 u | pe . pe \<in> GSupp1 u})"





 

end