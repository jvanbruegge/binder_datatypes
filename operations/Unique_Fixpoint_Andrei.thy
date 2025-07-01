theory Unique_Fixpoint_Andrei
  imports "Binders.MRBNF_Recursor" "../operations/BMV_Monad"
begin

declare supp_id_bound[simp, intro]

typedecl ('a1, 'a2, 'c1, 'c2) G
consts Gsub :: "('a1 :: var \<Rightarrow> 'a1) \<Rightarrow> ('a2 :: var \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G"
consts GFVrs1 :: "('a1 :: var, 'a2 :: var, 'c1, 'c2) G \<Rightarrow> 'a1 set"
consts GFVrs2 :: "('a1 :: var, 'a2 :: var, 'c1, 'c2) G \<Rightarrow> 'a2 set"
consts Gmap :: "('c1 \<Rightarrow> 'c1') \<Rightarrow> ('c2 \<Rightarrow> 'c2') \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1', 'c2') G"
consts GSupp1 :: "('a1 :: var, 'a2 :: var, 'c1, 'c2) G \<Rightarrow> 'c1 set"
consts GSupp2 :: "('a1 :: var, 'a2 :: var, 'c1, 'c2) G \<Rightarrow> 'c2 set"

pbmv_monad "('a1::var, 'a2::var, 'x1, 'x2) G"
  Sbs: Gsub
  RVrs: GFVrs1 GFVrs2
  Maps: Gmap
  Supps: GSupp1 GSupp2
  bd: natLeq
  sorry

print_theorems

definition GVrs :: "('a::var,'a,'c1,'c2) G \<Rightarrow> 'a set" where 
"GVrs u \<equiv> GFVrs1 u \<union> GFVrs2 u"

definition Gren :: 
"('a1 :: var \<Rightarrow> 'a1) \<Rightarrow> ('a2 :: var \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G" where 
"Gren \<rho>1 \<rho>2 u \<equiv> Gsub \<rho>1 \<rho>2 u"

(* *)
(*TODO: infer MrBNF properties for GVrs and Gren *)
(* *)

consts \<eta> :: "'a1 :: var \<Rightarrow> ('a1, 'a2 :: var, 'c1, 'c2) G"
consts \<eta>' :: "'a1 :: var \<Rightarrow> ('a1, 'a2 :: var, 'c1, 'c2) G"

lemma eta_natural: "Gren \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta> u)) = \<eta> (\<delta>1 u)"
  sorry
lemma eta'_natural: "Gren \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta>' u)) = \<eta>' (\<delta>1 u)"
  sorry

lemma eta_inj: "\<eta> a = \<eta> a' \<Longrightarrow> a = a'"
  sorry
lemma eta'_inj: "\<eta>' a = \<eta>' a' \<Longrightarrow> a = a'"
  sorry

lemma eta_distinct: "\<eta> a \<noteq> \<eta>' a'"
  sorry

typedecl 'a E

consts Ector :: "('a :: var, 'a, 'a E, 'a E) G \<Rightarrow> 'a E"
consts Eperm :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> 'a E \<Rightarrow> 'a E"
consts EVrs :: "(('a::var) E) \<Rightarrow> 'a set"

(* About these, you can assume any expression-like properties (so you can extend this, 
but please try to be non-redundant): *)
axiomatization where Eperm_id[simp]: "Eperm id = id"
and 
Eperm_comp:
"\<And> \<sigma> \<tau>. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
  Eperm \<sigma> o Eperm \<tau> = Eperm (\<sigma> o \<tau>)"
and 
EVrs_Eperm:
"\<And>\<delta> u. |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow> 
  EVrs (Eperm \<delta> u) \<subseteq> \<delta> ` EVrs u"
and 
EVrs_Ector:
"\<And>u. EVrs (Ector u::('a::var) E) \<subseteq> 
 GFVrs1 u \<union> \<Union> {EVrs e | e .  e \<in> GSupp1 u} \<union> \<Union> {EVrs e - GFVrs2 u | e .  e \<in> GSupp1 u}"
and 
Eperm_cong:
"\<And> \<sigma> \<tau> u. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow> 
  (\<forall>a\<in>EVrs u. \<sigma> a = \<tau> a) \<Longrightarrow> 
  Eperm \<sigma> u = Eperm \<tau> u"
and 
Ector_fresh_surj: "\<And>A e. |A::'a set| <o |UNIV :: 'a ::var set| \<Longrightarrow> 
\<exists>u. GFVrs2 u \<inter> A = {} \<and> e = Ector u"
and Ector_inject: 
"\<And> u v. (Ector u = Ector v) =
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and>
     |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (EVrs (Ector u)) \<sigma> \<and>
     Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u) = v)"


lemma Eperm_cong_id:
  "bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>  
  (\<forall>a\<in>EVrs u. \<sigma> a = a) \<Longrightarrow> 
  Eperm \<sigma> u = u"
  apply(rule Eperm_cong[where \<tau> = id, simplified]) by auto

lemma Ector_fresh_cases: 
"|A::'a set| <o |UNIV :: 'a ::var set| \<Longrightarrow> (\<And>u. e = Ector u \<Longrightarrow> GFVrs2 u \<inter> A = {} \<Longrightarrow> P) \<Longrightarrow> P"
using Ector_fresh_surj by blast


(* Definition of the BMV free variables *)

inductive Efreee for a where 
  "a \<in> GFVrs1 u \<Longrightarrow> \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow> Efreee a (Ector u)"
| "e \<in> GSupp1 u \<Longrightarrow> Efreee a e \<Longrightarrow> a \<notin> GFVrs2 u \<Longrightarrow> Efreee a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efreee a e \<Longrightarrow> Efreee a (Ector u)"

lemma Efreee_strong_induct: "|V| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efreee a x \<Longrightarrow>
(\<And>u. GFVrs2 u \<inter> V = {} \<Longrightarrow> a \<in> GFVrs1 u \<Longrightarrow> \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. GFVrs2 u \<inter> V = {} \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efreee a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GFVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. GFVrs2 u \<inter> V = {} \<Longrightarrow> e \<in> GSupp2 u \<Longrightarrow> Efreee a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P x"
  sorry
(* TODO: actually infer this *)

inductive Efree\<eta> for a where 
  "Efree\<eta> a (Ector (\<eta> a))"
| "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> a \<notin> GFVrs2 u \<Longrightarrow> Efree\<eta> a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> Efree\<eta> a (Ector u)"

lemma Efree\<eta>_strong_induct: "|V| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efree\<eta> a x \<Longrightarrow>
P (Ector (\<eta> a)) \<Longrightarrow>
(\<And>e u. GFVrs2 u \<inter> V = {} \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GFVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. e \<in> GSupp2 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P x"
  sorry
(* TODO: actually infer this *)

inductive Efree\<eta>' for a where 
  "Efree\<eta>' a (Ector (\<eta>' a))"
| "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> a \<notin> GFVrs2 u \<Longrightarrow> Efree\<eta>' a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> Efree\<eta>' a (Ector u)"

lemma Efree\<eta>'_strong_induct: "|V| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efree\<eta>' a x \<Longrightarrow>
P (Ector (\<eta>' a)) \<Longrightarrow>
(\<And>e u. GFVrs2 u \<inter> V = {} \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GFVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. e \<in> GSupp2 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P x"
  sorry
(* TODO: actually infer this *)

definition "EFVrs e = {a. Efreee a e}"
definition "EFVrs\<eta> e = {a. Efree\<eta> a e}"
definition "EFVrs\<eta>' e = {a. Efree\<eta>' a e}"

(* Definition of the BMV substitution by the unique fixpoint principle *)

consts Esub :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a ::var \<Rightarrow> 'a E) \<Rightarrow> ('a ::var \<Rightarrow> 'a E) \<Rightarrow> 'a E \<Rightarrow> 'a E"

axiomatization where 
Esub_Ector:
"\<And>u \<delta> \<rho> \<rho>'. |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow> 
 |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
 |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|
 \<Longrightarrow> 
 (\<forall>a. Esub \<delta> \<rho> \<rho>' (Ector (\<eta> a)) = \<rho> a)
 \<and>
 (\<forall> a. Esub \<delta> \<rho> \<rho>' (Ector (\<eta>' a)) = \<rho>' a)
 \<and> 
 (GFVrs2 u \<inter> imsupp \<delta> = {} \<and> 
    GFVrs2 u \<inter> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> = {} \<and> 
    GFVrs2 u \<inter> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' = {} \<and>
    (\<forall>a. u \<noteq> \<eta> a) \<and> (\<forall>a'. u \<noteq> \<eta>' a') \<longrightarrow> 
    Esub \<delta> \<rho> \<rho>' (Ector u) = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u)))"
and Eperm_Esub:
  "\<And>\<sigma> \<delta> \<rho> \<rho>'. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
  |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
  |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  Eperm \<sigma> o Esub \<delta> \<rho> \<rho>' = Esub (\<sigma> o \<delta> o inv \<sigma>) (Eperm \<sigma> o \<rho> o inv \<sigma>) (Eperm \<sigma> o \<rho>' o inv \<sigma>)"
and EVrs_sub:
  "\<And>e \<delta> \<rho> \<rho>'. |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
  |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  EVrs (Esub \<delta> \<rho> \<rho>' e) \<subseteq> EVrs e \<union> supp \<delta> \<union> SSupp (Ector o \<eta>) \<rho>  \<union> SSupp (Ector o \<eta>') \<rho>'"
and 
Esub_unique_fresh_relativized:
  "\<And>\<delta> \<rho> \<rho>' e B B\<eta> B\<eta>' A h. |- B| <o |UNIV :: 'a set| \<Longrightarrow>
  |- B\<eta>| <o |UNIV :: 'a set| \<Longrightarrow> 
  |- B\<eta>'| <o |UNIV :: 'a set| \<Longrightarrow>
  |A| <o |UNIV::'a set| \<Longrightarrow> 
  |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow> 
  |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow> 
  |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow> 
  (\<And>a. a \<in> B\<eta> \<Longrightarrow> h (Ector (\<eta> a)) = \<rho> a) \<Longrightarrow> 
  (\<And>a. a \<in> B\<eta>' \<Longrightarrow> h (Ector (\<eta>' a)) = \<rho>' a) \<Longrightarrow> 
  (\<And>u.
   EFVrs (Ector u) \<subseteq> B \<Longrightarrow>
   EFVrs\<eta> (Ector u) \<subseteq> B\<eta> \<Longrightarrow>
   EFVrs\<eta>' (Ector u) \<subseteq> B\<eta>' \<Longrightarrow>
   GFVrs2 u \<inter> A = {} \<Longrightarrow>
   GFVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GFVrs2 u \<inter> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> = {} \<Longrightarrow>
   GFVrs2 u \<inter> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' = {} \<Longrightarrow>
   \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
   h (Ector u) = Ector (Gsub \<delta> id (Gmap h h u)))
  \<Longrightarrow> 
  EFVrs e \<subseteq> B \<Longrightarrow> EFVrs\<eta> e \<subseteq> B\<eta> \<Longrightarrow> EFVrs\<eta>' e \<subseteq> B\<eta>' \<Longrightarrow> h e = Esub \<delta> \<rho> \<rho>' e"

(* *)

lemmas Esub_Ector1 = Esub_Ector[THEN conjunct1, rule_format]
lemmas Esub_Ector2 = Esub_Ector[THEN conjunct2, THEN conjunct1, rule_format]
lemmas Esub_Ector3 = Esub_Ector[THEN conjunct2, THEN conjunct2, rule_format]

definition "Sp \<delta> \<rho> \<rho>' \<equiv>
imsupp \<delta> \<union> IImsupp (Ector \<circ> \<eta>) EFVrs\<eta> \<rho> \<union> IImsupp (Ector \<circ> \<eta>') EFVrs\<eta>' \<rho>'"

definition "smBj \<delta> \<rho> \<rho>' \<equiv> |supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set| \<and> 
   |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<and> 
   |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
 
lemma Esub_Ector_3: "smBj \<delta> \<rho> \<rho>' \<Longrightarrow> GFVrs2 u \<inter> Sp \<delta> \<rho> \<rho>' = {} \<Longrightarrow> 
\<forall>a. u \<noteq> \<eta> a \<Longrightarrow>
\<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
Esub \<delta> \<rho> \<rho>' (Ector u) = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u))"
apply(rule Esub_Ector3) unfolding smBj_def Sp_def by auto

lemma Gsub_Gmap_cong: 
assumes "|supp \<sigma>1| <o |UNIV::('a::var) set|"
"|supp \<sigma>2| <o |UNIV::('a::var) set|"
"|supp \<tau>1| <o |UNIV::('a::var) set|"
"|supp \<tau>2| <o |UNIV::('a::var) set|"
"\<And>a1. a1 \<in> GFVrs1 (u::('a,'a,'b,'c) G) \<Longrightarrow> \<sigma>1 a1 = \<tau>1 a1"
"\<And>a2. a2 \<in> GFVrs2 u \<Longrightarrow> \<sigma>2 a2 = \<tau>2 a2" 
"\<And>a1. a1 \<in> GSupp1 u \<Longrightarrow> f1 a1 = g1 a1"
"\<And>a2. a2 \<in> GSupp2 u \<Longrightarrow> f2 a2 = g2 a2"
shows "Gsub \<sigma>1 \<sigma>2 (Gmap f1 f2 u) = Gsub \<tau>1 \<tau>2 (Gmap g1 g2 u)" 
proof-
  have 0: "Gmap f1 f2 u = Gmap g1 g2 u"
  apply(rule G.Map_cong) using assms by auto
  show ?thesis unfolding 0 apply(rule G.Sb_cong)
  using assms by (auto simp: G.Vrs_Map)   
qed

lemma Gmap_Gsub: "|supp (\<sigma>1::'a\<Rightarrow>'a)| <o |UNIV::'a::var set| \<Longrightarrow> 
 |supp (\<sigma>2::'a\<Rightarrow>'a)| <o |UNIV::'a::var set| \<Longrightarrow> 
Gmap f1 f2 (Gsub \<sigma>1 \<sigma>2 u) = Gsub \<sigma>1 \<sigma>2 (Gmap f1 f2 u)"
using G.Map_Sb[unfolded o_def fun_eq_iff, rule_format] .  

lemma Gmap_comp: "Gmap f1 f2 (Gmap g1 g2 (u::('a::var,'a,'b,'c)G)) = Gmap (f1 o g1) (f2 o g2) u"
using G.Map_comp[unfolded o_def fun_eq_iff, rule_format] unfolding o_def .

lemma Gsub_comp: "|supp (\<sigma>1::'a\<Rightarrow>'a)| <o |UNIV::'a::var set| \<Longrightarrow> 
 |supp (\<sigma>2::'a\<Rightarrow>'a)| <o |UNIV::'a::var set| \<Longrightarrow> 
 |supp (\<tau>1::'a\<Rightarrow>'a)| <o |UNIV::'a::var set| \<Longrightarrow> 
 |supp (\<tau>2::'a\<Rightarrow>'a)| <o |UNIV::'a::var set| \<Longrightarrow> 
Gsub \<tau>1 \<tau>2 (Gsub \<sigma>1 \<sigma>2 u) = Gsub (\<tau>1 o \<sigma>1) (\<tau>2 o \<sigma>2) u"
using G.Sb_comp[unfolded o_def fun_eq_iff, rule_format] unfolding o_def .   

lemma Esub_eq_Ector: 
assumes sm: "smBj \<delta> \<rho> \<rho>'" and fr: "GFVrs2 u' \<inter> Sp \<delta> \<rho> \<rho>' = {}"
and sb: "Esub \<delta> \<rho> \<rho>' e = Ector u'"  
and u_nonEta: "\<forall>a. u \<noteq> \<eta> a" "\<forall>a. u \<noteq> \<eta>' a"
shows "\<exists>u. GFVrs2 u \<inter> Sp \<delta> \<rho> \<rho>' = {} \<and> 
   u' = Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u)"
(* 
proof-
  obtain v where fr': "GFVrs2 v \<inter> Sp \<delta> \<rho> \<rho>' = {}" and e: "e = Ector v" sorry
  have v_nonEta: "\<forall>a. v \<noteq> \<eta> a" "\<forall>a. v \<noteq> \<eta>' a" sorry
  have "Ector u' = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') v))"
  using sb unfolding e apply(subst (asm) Esub_Ector_3) 
  using fr' sm v_nonEta by auto
  then obtain \<sigma> where sig: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a set|"
      "id_on (GFVrs1 u' \<union> (\<Union> (EVrs ` GSupp1 u') - GFVrs2 u')) \<sigma>"
  and sig_sub: "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u') = 
      Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') v)"  
  unfolding Ector_inject by auto 
  have u': "u' = 
  Gsub id (inv \<sigma>) (Gmap (Eperm (inv \<sigma>)) id (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') v)))"
  using sig_sub sorry
  (*have 0: "GFVrs1 u' \<union> (\<Union> (EVrs ` GSupp1 u') - GFVrs2 u') = 
    GFVrs1 v \<union> (\<Union> (EVrs ` GSupp1 v) - GFVrs2 v)"
  unfolding u'  apply auto apply(subst (asm) G.Vrs_Sb) unfolding G.Vrs_Map apply auto
  subgoal sorry apply(subst (asm) G.Vrs_Sb) unfolding G.Vrs_Map apply auto
  subgoal sorry sledgehammer
  *)
  have sig_rho: "imsupp \<sigma> \<inter> Sp \<delta> \<rho> \<rho>' = {}" sorry (* by choosing different \<delta> \<rho> \<rho>' and using congruence *)

  have 1: "Gmap (Eperm (inv \<sigma>) \<circ> Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') v = 
           Gmap (Esub \<delta> \<rho> \<rho>' o Eperm (inv \<sigma>)) (Esub \<delta> \<rho> \<rho>') v"
  apply(rule G.Map_cong)
    subgoal for u apply simp sorry (* from parameterized recursion *)
    subgoal by simp .
  show ?thesis apply(rule exI[of _ "Gsub id (inv \<sigma>) (Gmap (Eperm (inv \<sigma>)) id v)"])
  apply safe
    subgoal for a apply(subst (asm) G.Vrs_Sb(2)) subgoal sorry subgoal sorry
    apply(subst (asm) G.Vrs_Map(2)) using fr' 
    using not_in_imsupp_same sig(1) sig_rho by fastforce 
    subgoal unfolding u' apply(subst Gmap_Gsub[where ?f1.0 = "Eperm (inv \<sigma>)"])
      subgoal sorry subgoal sorry
      subgoal apply(subst Gsub_comp) subgoal sorry subgoal sorry subgoal sorry
      unfolding Gmap_comp apply simp
      unfolding 1 apply(subst G.Sb_cong) apply auto
      subgoal sorry subgoal sorry subgoal sorry subgoal sorry
      apply(subst Gmap_Gsub[symmetric]) subgoal sorry subgoal sorry
      apply(subst Gmap_Gsub[symmetric]) subgoal sorry subgoal sorry
      apply(subst Gmap_Gsub[symmetric]) subgoal sorry subgoal sorry
      apply(subst Gmap_Gsub[symmetric]) subgoal sorry subgoal sorry
      unfolding Gmap_comp apply simp apply(subst Gsub_comp) 
      subgoal sorry subgoal sorry subgoal sorry apply simp . . .  
qed
*)
(* you can assume this :*)
sorry



(* *)


pbmv_monad "'a::var E"
  Sbs: Esub
  RVrs: EFVrs
  Injs: "Ector o \<eta>" "Ector o \<eta>'"
  Vrs: EFVrs\<eta> EFVrs\<eta>'
  bd: natLeq
sorry

end