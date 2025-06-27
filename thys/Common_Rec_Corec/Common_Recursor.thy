theory Common_Recursor
  imports "HOL-Library.Countable_Set_Type"
begin

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

(* nominal-like structures: *)
definition nom :: "((var \<Rightarrow> var) \<Rightarrow> 'E \<Rightarrow> 'E) \<Rightarrow> ('E \<Rightarrow> var set) \<Rightarrow> bool" where 
"nom perm Vrs \<equiv> 
 (\<forall>\<sigma>1 \<sigma>2. small \<sigma>1 \<and> bij \<sigma>1 \<and> small \<sigma>2 \<and> bij \<sigma>2 \<longrightarrow>  
 perm (\<sigma>1 o \<sigma>2) = perm \<sigma>1 o perm \<sigma>2) 
 \<and>
 (\<forall>\<sigma>1 \<sigma>2 e'. 
  small \<sigma>1 \<and> bij \<sigma>1 \<and> small \<sigma>2 \<and> bij \<sigma>2 \<and>  
  (\<forall>a\<in>Vrs e'. \<sigma>1 a = \<sigma>2 a) \<longrightarrow> 
  perm \<sigma>1 e' = perm \<sigma>2 e')"


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

lemma Gmap_id'[simp]: "Gmap (\<lambda>x. x) (\<lambda>x. x) = id"
using Gmap_id unfolding id_def .

typedecl E

consts Ector :: "(E,E) G \<Rightarrow> E"
consts Eperm :: "(var \<Rightarrow> var) \<Rightarrow> E \<Rightarrow> E"
consts EVrs :: "E \<Rightarrow> var set"

axiomatization where Ector_surj: "\<And>e. \<exists>u. Ector u = e"

definition Edtor :: "E \<Rightarrow> ((E,E) G) set" where 
"Edtor e = {u . Ector u = e}"

lemma in_Edtor_Ector: "v \<in> Edtor (Ector u) \<longleftrightarrow> Ector v = Ector u"
unfolding Edtor_def by auto

lemma Edtor_NE: "Edtor e \<noteq> {}"
unfolding Edtor_def using Ector_surj by auto

lemma Ector_exhaust: "(\<And>u. P (Ector u)) \<Longrightarrow> (\<forall>e. P e)"
by (metis Ector_surj)

lemma Ector_exhaust': "(\<And>u. e = Ector u \<Longrightarrow> P e) \<Longrightarrow> P e"
by (metis Ector_surj)

lemma nom: "nom Eperm EVrs"
sorry

(* Corresponds to ctorPermM *)
lemma Eperm_Ector: "small \<sigma> \<Longrightarrow> bij \<sigma>  \<Longrightarrow> 
       Eperm \<sigma> (Ector u') = 
       Ector (Gren \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u'))"
sorry

(* Corresponds to ctorVarsM *)
lemma EVrs_Ector: "EVrs (Ector u) =
     GVrs1 u \<union> 
     (\<Union> {EVrs e' | e' . e' \<in> GSupp1 u}) \<union> 
     (\<Union> {EVrs e' - GVrs2 u | e' . e' \<in> GSupp1 u})"
sorry

(* *)
lemma Edtor_Eperm: "small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> 
  Edtor (Eperm \<sigma> e) \<subseteq> Gren \<sigma> \<sigma> ` (Gmap (Eperm \<sigma>) (Eperm \<sigma>) ` (Edtor e))"
unfolding Edtor_def image_def using Eperm_Ector apply auto sorry
(* proof using constructor property and inverse permutatiobs *)



lemma Edtor_eq_imp: 
"Ector u1 = Ector u2 \<Longrightarrow>
   (\<exists>\<sigma>. small \<sigma> \<and> bij \<sigma> \<and> 
        supp \<sigma> \<subseteq> GVrs1 u1 \<union> 
                 (\<Union> {EVrs e | e . e \<in> GSupp1 u1}) \<union> 
                 (\<Union> {EVrs e - GVrs2 u1 | e . e \<in> GSupp1 u1}) \<and> 
        u2 = Gren id \<sigma> u1)"
sorry

lemma Edtor_EVrs: 
"u\<in>Edtor e \<Longrightarrow> 
 GVrs1 u \<union> 
 (\<Union> {EVrs e | e . e \<in> GSupp1 u}) \<union> 
 (\<Union> {EVrs e - GVrs2 u | e . e \<in> GSupp1 u}) 
 \<subseteq> 
 EVrs e" 
sorry


(* *)
type_synonym E' = E 


definition dtorNeC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> bool" where 
"dtorNeC dtor \<equiv> \<forall>e U. dtor e = Inl U \<longrightarrow> U \<noteq> {}"

definition dtorPermC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> bool" 
where "dtorPermC dtor perm \<equiv> 
\<forall>\<sigma> e. small \<sigma> \<and> bij \<sigma> \<longrightarrow> 
  (\<forall> U. dtor e = Inl U \<longrightarrow> (\<exists>U'. dtor (perm \<sigma> e) = Inl U' \<and> U' \<subseteq> Gren \<sigma> \<sigma> ` (Gmap (perm \<sigma>) (perm \<sigma>) ` U)))
  \<and> 
  (\<forall>e1. dtor e = Inr e1 \<longrightarrow> (\<exists>e1'. dtor (perm \<sigma> e) = Inr e1' \<and> e1' =  Eperm \<sigma> e1))"

definition dtorVrsGrenC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> ('E' \<Rightarrow> var set) \<Rightarrow> bool" 
where
"dtorVrsGrenC dtor Vrs \<equiv> 
 (\<forall>e U u1 u2. dtor e = Inl U \<and> {u1,u2} \<subseteq> U \<longrightarrow> 
   (\<exists>\<sigma>. small \<sigma> \<and> bij \<sigma> \<and> 
        supp \<sigma> \<subseteq> GVrs1 u1 \<union> 
                 (\<Union> {Vrs e | e . e \<in> GSupp1 u1}) \<union> 
                 (\<Union> {Vrs e - GVrs2 u1 | e . e \<in> GSupp1 u1}) \<and> 
        u2 = Gren id \<sigma> u1))"



definition dtorVrsC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> ('E' \<Rightarrow> var set) \<Rightarrow> bool" 
where
"dtorVrsC dtor Vrs \<equiv> 
 (\<forall>e.  
  (\<forall>U. dtor e = Inl U \<longrightarrow> 
       (\<forall>u\<in>U. GVrs1 u \<union> 
              (\<Union> {Vrs e | e . e \<in> GSupp1 u}) \<union> 
              (\<Union> {Vrs e - GVrs2 u | e . e \<in> GSupp1 u}) 
              \<subseteq> 
              Vrs e)) 
  \<and>  
  (\<forall>e1. dtor e = Inr e1 \<longrightarrow> EVrs e1 \<subseteq> Vrs e)
)"



(* Full-recursion comodel: I keep E' as an abbreviation for E to avoid confusion: *)
locale Comodel =
fixes (* no set V, as we need no Barendregt convention here *)
Edtor' :: "E' \<Rightarrow> ((E',E')G) set + E" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' :: "E' \<Rightarrow> var set" 
assumes 
nom: "nom Eperm' EVrs'" 
and  
dtorNeC: "dtorNeC Edtor'"
and 
dtorPermC: "dtorPermC Edtor' Eperm'"
and 
dtorVrsGrenC: "dtorVrsGrenC Edtor' EVrs'"
and 
dtorVrsC: "dtorVrsC Edtor' EVrs'"
begin 


definition corec :: "E \<Rightarrow> E'" where 
"corec = undefined"

lemma corec_Edtor_Inl:
assumes "comodel"
shows "Edtor' e = Inl U \<Longrightarrow> Gmap corec corec ` U  \<subseteq> Edtor (corec e)"
sorry

lemma corec_Edtor_Inr:
"Edtor' e = Inr e1 \<Longrightarrow> corec e = e1"
sorry

lemma corec_Eperm:
"small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> supp \<sigma> \<inter> V = {} \<Longrightarrow> 
 corec (Eperm' \<sigma> e') = Eperm \<sigma> (corec e')"
sorry

lemma rec_EVrs:
"EVrs (corec e') \<subseteq> EVrs' e'"
sorry

lemma corec_unique: 
assumes "\<And> e U. Edtor' e = Inl U \<Longrightarrow> Gmap H H ` U  \<subseteq> Edtor (corec e)"
and "\<And>e e1. Edtor' e = Inr e1 \<Longrightarrow> H e = e1"
shows "H = corec"
sorry

end (* locale Comodel *)


(****)
(* Iteration Barendregt-enriched model (full-recursion not needed), but for codomain equal to E; 
I keep E' as an abbreviation to avoid confusion. *)

typedecl P 
consts Pperm :: "(var \<Rightarrow> var) \<Rightarrow> P \<Rightarrow> P" 
consts PVrs :: "P \<Rightarrow> var set"
axiomatization where nomP: "nom Pperm PVrs"
and countable_PVrs: "\<And>p. countable (PVrs p)"
and PVrs_Pperm: "\<And> \<sigma> p. bij \<sigma> \<Longrightarrow> small \<sigma> \<Longrightarrow> PVrs (Pperm \<sigma> u) = \<sigma> ` PVrs u"

definition lift :: "((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> (P\<Rightarrow>'E') \<Rightarrow> (P=>'E'))" where 
"lift perm \<sigma> pe p \<equiv> perm \<sigma> (pe (Pperm (inv \<sigma>) p))"

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



locale Model =
fixes Ector' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' ::"E' \<Rightarrow> var set" 
assumes nom: "nom Eperm' EVrs'"
and ctorPermM: "\<And>u. ctorPermM Ector' Eperm' u"
and ctorVarsM: "\<And>u. ctorVarsM Ector' EVrs' u"
begin 


definition rec :: "E \<Rightarrow> P\<Rightarrow>E'" where 
"rec = undefined"

lemma rec_Ector:
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow>  
 rec (Ector u) p = Ector' (Gmap rec rec u) p"
sorry

lemma rec_Eperm:
"small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow>  
 rec (Eperm \<sigma> e) p = Eperm' \<sigma> (rec e (Pperm (inv \<sigma>) p))"
sorry

lemma rec_EVrs: 
"EVrs' (rec e p) \<subseteq> PVrs p \<union> EVrs e"
sorry


lemma rec_unique:
assumes "\<And>u. GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> H (Ector u) p = Ector' (Gmap H H u) p"
shows "H = rec" 
sorry

end (* locale Model *)

(******)


consts \<phi> :: "('e,'e) G \<Rightarrow> bool"
axiomatization where \<phi>_Gmap: "\<And> u f g. \<phi> (Gmap f g u) \<longleftrightarrow> \<phi> u"
axiomatization where \<phi>_Gren: "\<And> u \<sigma>. small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> \<phi> (Gren \<sigma> \<sigma> u) \<longleftrightarrow> \<phi> u"

(*
definition ctor0PermM :: "var set \<Rightarrow> (('E,'E) G \<Rightarrow> 'E') \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') 
 \<Rightarrow> bool" where 
"ctor0PermM V ctor0 perm \<equiv> 
(\<forall>u \<sigma>. \<phi> u \<and> 
       small \<sigma> \<and> bij \<sigma> \<and> supp \<sigma> \<inter> V = {} \<longrightarrow> 
       perm \<sigma> (ctor0 u) = 
       ctor0 (Gren \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)))"

definition ctor1PermM :: "var set \<Rightarrow> (('E','E') G \<Rightarrow> 'E') \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') 
 \<Rightarrow> bool" where 
"ctor1PermM V ctor1 perm \<equiv> 
(\<forall>u' \<sigma>. \<not> \<phi> u' \<and> 
       small \<sigma> \<and> bij \<sigma> \<and> supp \<sigma> \<inter> V = {} \<longrightarrow> 
       perm \<sigma> (ctor1 u') = 
       ctor1 (Gren \<sigma> \<sigma> (Gmap (perm \<sigma>) (perm \<sigma>) u')))"

definition ctor0VarsM :: "var set \<Rightarrow> ((E,E) G \<Rightarrow> 'E') \<Rightarrow> ('E' \<Rightarrow> var set)
\<Rightarrow> bool" where 
"ctor0VarsM V ctor Vrs \<equiv> 
 \<forall>u. \<phi> u \<longrightarrow> 
     Vrs (ctor u) \<subseteq> V \<union> 
     GVrs1 u \<union> 
     (\<Union> {EVrs e | e . e \<in> GSupp1 u}) \<union> 
     (\<Union> {EVrs e - GVrs2 u | e . e \<in> GSupp1 u})"

definition ctor1VarsM :: "var set \<Rightarrow> (('E','E') G \<Rightarrow> 'E') \<Rightarrow> ('E' \<Rightarrow> var set)
\<Rightarrow> bool" where 
"ctor1VarsM V ctor Vrs \<equiv>  
 \<forall>u. \<not> \<phi> u \<longrightarrow> 
     Vrs (ctor u) \<subseteq> V \<union>  
     GVrs1 u \<union> 
     (\<Union> {Vrs e' | e' . e' \<in> GSupp1 u}) \<union> 
     (\<Union> {Vrs e' - GVrs2 u | e' . e' \<in> GSupp1 u})"
*)


locale Special_Model = 
fixes Ector0' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'" 
and Ector1' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' ::"E' \<Rightarrow> var set" 
assumes nom: "nom Eperm' EVrs'"
and ctor0PermM: "\<And>u. \<phi> u \<Longrightarrow> ctorPermM Ector0' Eperm' u" and 
    ctor1PermM: "\<And>u. \<not> \<phi> u \<Longrightarrow> ctorPermM Ector1' Eperm' u"
and ctor0VarsM: "\<And>u. \<phi> u \<Longrightarrow> ctorVarsM Ector0' EVrs' u" and 
    ctor1VarsM: "\<And>u. \<not> \<phi> u \<Longrightarrow> ctorVarsM Ector1' EVrs' u"
begin

(* 1. Recursion principle by associating a model to a special-model: *)

definition Ector' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'" where 
"Ector' u \<equiv> if \<phi> u then Ector0' u else Ector1' u"

lemma Ector'_\<phi>[simp]: "\<phi> u \<Longrightarrow> Ector' u = Ector0' u"
unfolding Ector'_def by auto

lemma Ector'_not\<phi>[simp]: "\<not> \<phi> u \<Longrightarrow> Ector' u = Ector1' u"
unfolding Ector'_def by auto

lemma ctorPermM: "ctorPermM Ector' Eperm' u"
unfolding ctorPermM_def apply safe
  subgoal for \<sigma> apply(cases "\<phi> u")
    subgoal unfolding Ector'_\<phi>  
    apply(subst ctor0PermM[unfolded ctorPermM_def, rule_format])
      subgoal .
      subgoal by auto
      subgoal apply(subst Ector'_\<phi> )
        subgoal using \<phi>_Gmap \<phi>_Gren by fastforce
        subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . .
    subgoal unfolding Ector'_not\<phi>  
    apply(subst ctor1PermM[unfolded ctorPermM_def, rule_format])
      subgoal .
      subgoal using \<phi>_Gmap by auto
      subgoal apply(subst Ector'_not\<phi>)
        subgoal using \<phi>_Gmap \<phi>_Gren by fastforce
        subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . . . .

lemma ctorVarsM: "ctorVarsM Ector' EVrs' u"
unfolding ctorVarsM_def  
  apply(cases "\<phi> u")
    subgoal unfolding Ector'_\<phi>  apply(intro allI)  
    apply(rule subset_trans[OF ctor0VarsM[unfolded ctorVarsM_def, rule_format]])
    by auto 
    subgoal unfolding Ector'_not\<phi> apply(intro allI) 
    apply(rule subset_trans[OF ctor1VarsM[unfolded ctorVarsM_def, rule_format]]) 
    using \<phi>_Gmap by auto . 


(* special-models form models: *)
sublocale Model where Ector' = Ector' and Eperm' = Eperm' and EVrs' = EVrs' 
apply standard 
using nom ctorPermM ctorVarsM by auto 


(* and now we customize their recursion theorems: *)
thm rec_Ector rec_Eperm rec_unique 
(* NB: these stay the same: *) thm rec_EVrs rec_Eperm

 
lemma rec_Ector_\<phi>:
assumes "\<phi> u"    
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> rec (Ector u) p = Ector0' (Gmap rec rec u) p"
apply(subst rec_Ector) 
  subgoal using assms by simp
  subgoal using assms apply(subst Ector'_\<phi>)
    subgoal using \<phi>_Gmap by auto
    subgoal unfolding Gmap_comp unfolding o_def by simp . .

lemma rec_Ector_not_\<phi>:
assumes "\<not> \<phi> u"  
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> rec (Ector u) p = Ector1' (Gmap rec rec u) p"
apply(subst rec_Ector)
  subgoal using assms by simp 
  subgoal using assms apply(subst Ector'_not\<phi>)
    subgoal using \<phi>_Gmap by auto
    subgoal unfolding Gmap_comp unfolding o_def by simp . .

lemma rec_unique':
assumes "\<And>u p. GVrs2 u \<inter> PVrs p = {} \<Longrightarrow>
 (\<phi> u \<longrightarrow> H (Ector u) p = Ector0' (Gmap H H u) p)
 \<and>
 (\<not> \<phi> u \<longrightarrow> H (Ector u) p = Ector1' (Gmap H H u) p)"
shows "H = rec" 
apply(rule rec_unique) 
using assms by (simp add: Ector'_def \<phi>_Gmap)  


end (* locale Special_Model *)


locale Special_Model_Plus = Special_Model Ector0' Ector1' Eperm' EVrs'
for Ector0' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'" 
and Ector1' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'"
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' ::"E' \<Rightarrow> var set" + 
assumes Ector_\<phi>_inj: "\<And>u1 u2. \<phi> u1 \<Longrightarrow> \<comment> \<open>\<phi> u2 \<Longrightarrow>  \<close> Ector u1 = Ector u2 \<Longrightarrow> u1 = u2"
and Eperm'_Eperm: "Eperm' = Eperm"
and EVrs'_EVrs: "EVrs' = EVrs"
(* and \<phi>_GVrs2: "\<And>u::(E,E) G. \<phi> u \<Longrightarrow> GVrs2 u = {}" (* no binders in items satisfying \<phi> *) *)
(* 
and EVrs'_\<phi>: "\<And>u. \<phi> u \<Longrightarrow> EVrs' (Ector u) = EVrs (Ector0' u)"
and EVrs'_not\<phi>: "\<And>u. \<not> \<phi> u \<Longrightarrow> EVrs' (Ector u) = EVrs (Ector1' u)"
*)
and Ector1_Ector: "\<And>u u1 p. \<not> \<phi> u \<Longrightarrow> \<not> \<phi> u1 \<Longrightarrow> 
   GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u1 \<inter> PVrs p = {} \<Longrightarrow> 
   Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u1) \<Longrightarrow> 
   Ector1' u p = Ector1' u1 p"
(* Ector1 is less injective that Ector outside \<phi>, and assuming freshness *)
begin 

(* 2. Corecursion principle by associating a comodel to a special-model: *)

lemma Ector_\<phi>: "Ector u = Ector v \<Longrightarrow> \<phi> u \<longleftrightarrow> \<phi> v"
using Ector_\<phi>_inj by metis

lemma \<phi>_Some_Ector: "\<phi> u \<Longrightarrow> (SOME ua. Ector ua = Ector u) = u"
by (metis (mono_tags, lifting) Ector_\<phi>_inj tfl_some) 

lemma \<phi>_Some_Ector': "\<phi> (SOME ua. Ector ua = Ector u) \<longleftrightarrow> \<phi> u"
by (metis (mono_tags, lifting) Ector_\<phi>_inj tfl_some) 


fun Edtor1' :: "P\<times>E' \<Rightarrow> ((P\<times>E',P\<times>E')G) set" where 
"Edtor1' (p,e) =
\<Union> { {u1 . Ector (Gmap snd snd u1) = Ector1' u p \<and> 
          GSupp1 (Gmap fst fst u1) \<union>  GSupp2 (Gmap fst fst u1) \<subseteq> {p} \<and> 
          GVrs2 u1 \<inter> PVrs p = {}} | 
       u . \<not> \<phi> u \<and> Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = e \<and> GVrs2 u \<inter> PVrs p = {}}"
declare Edtor1'.simps[simp del]
lemmas Edtor1'_def = Edtor1'.simps

(* A \<Rightarrow> (P\<Rightarrow>A)*)

lemma in_Edtor1'_Ector_aux: 
assumes "\<not> \<phi> u" "GVrs2 u \<inter> PVrs p = {}" 
shows "u1 \<in> Edtor1' (p,Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u)) \<longleftrightarrow> 
  (Ector (Gmap snd snd u1) = Ector1' u p \<and> 
   GSupp1 (Gmap fst fst u1) \<union> GSupp2 (Gmap fst fst u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {})"
using assms unfolding Edtor1'_def apply auto apply(rule Ector1_Ector) by auto

lemma in_Edtor1'_Ector: 
assumes "\<not> \<phi> u" "GVrs2 u \<inter> PVrs p = {}" 
shows "u1 \<in> Edtor1' (p,Ector u) \<longleftrightarrow> 
  (Ector (Gmap snd snd u1) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
   GSupp1 (Gmap fst fst u1) \<union> GSupp2 (Gmap fst fst u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {})"
proof-
  define v where v: "v \<equiv> Gmap (\<lambda>e (p::P). e) (\<lambda>e (p::P). e) u"
  have u: "u = Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) v"
  unfolding v Gmap_comp o_def by simp
  show ?thesis using assms apply(subst u)  
    by (simp add: GVrs2_Gmap \<phi>_Gmap in_Edtor1'_Ector_aux v)
qed

 

lemma Edtor1'_Ector: 
assumes "\<not> \<phi> u" "GVrs2 u \<inter> PVrs p = {}" 
shows "Edtor1' (p,Ector u) = 
  {u1 . Ector (Gmap snd snd u1) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
        GSupp1 (Gmap fst fst u1) \<union> GSupp2 (Gmap fst fst u1) \<subseteq> {p} \<and> 
        GVrs2 u1 \<inter> PVrs p = {}}"
using in_Edtor1'_Ector[OF assms] by auto

(*
lemma Edtor1'_Ector: "\<not> \<phi> u \<Longrightarrow> Edtor1' (Ector u) = {u1 . GVrs2 u1 \<inter> V = {} \<and> Ector u1 = Ector1' u}" 
unfolding Edtor1'_def Edtor_def apply auto using Ector1_Ector by blast
*)


fun Edtor' :: "P\<times>E' \<Rightarrow> ((P\<times>E',P\<times>E')G)set + E" where 
"Edtor' (p,e) = (let u = (SOME u. u \<in> Edtor e) in 
  if \<phi> u then Inr (Ector0' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p) else Inl (Edtor1' (p,e)))"
declare Edtor'.simps[simp del]
lemmas Edtor'_def = Edtor'.simps

lemma Edtor'_\<phi>: 
assumes "\<phi> u"
shows "Edtor' (p, Ector u) = Inr (Ector0' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p)"
using assms unfolding Edtor'_def
unfolding in_Edtor_Ector by (auto simp: Let_def \<phi>_Some_Ector)

lemma Edtor'_not\<phi>: 
assumes "\<not> \<phi> u"
shows "Edtor' (p, Ector u) = Inl (Edtor1' (p, Ector u))"
using assms unfolding Edtor'_def 
unfolding in_Edtor_Ector by (auto simp: Let_def \<phi>_Some_Ector')  

(* *)
lemma Edtor1'_NE: 
assumes \<phi>: "\<not> \<phi> u" 
shows "Edtor1' (p, Ector u) \<noteq> {}" using in_Edtor1'_Ector
proof-
  obtain u0 where u0u: "Ector u0 = Ector u" and g: "GVrs2 u0 \<inter> PVrs p = {}" 
  using countable_PVrs sorry (* OK *)
  hence \<phi>: "\<not> \<phi> u0" using \<phi> using Ector_\<phi> by blast
  obtain uu1 where "Ector uu1 = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u0) p" "GVrs2 uu1 \<inter> PVrs p = {}" 
  using countable_PVrs sorry (* OK *)
  then have "Gmap (Pair p) (Pair p) uu1 \<in> Edtor1' (p, Ector u)" 
  unfolding u0u[symmetric] apply(subst in_Edtor1'_Ector[OF \<phi> g]) apply safe
    subgoal unfolding Gmap_comp o_def by simp
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal unfolding GVrs2_Gmap by auto .
  thus ?thesis by auto
qed

lemma dtorNeC: "dtorNeC Edtor'"
unfolding dtorNeC_def apply safe
  subgoal for p e U  apply(rule Ector_exhaust'[of e]) apply simp
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi> using Edtor1'_NE by simp . . .

fun EVrs'' where "EVrs'' (p,e) = EVrs e \<union> PVrs p"
declare EVrs''.simps[simp del]
lemmas EVrs''_def = EVrs''.simps

fun Eperm'' where "Eperm'' \<sigma> (p,e) = (Pperm \<sigma> p, Eperm \<sigma> e)"
declare Eperm''.simps[simp del]
lemmas Eperm''_def = Eperm''.simps

lemma snd_EPerm''[simp]: "snd \<circ> Eperm'' \<sigma> = Eperm \<sigma> o snd"
unfolding fun_eq_iff by (simp add: Eperm''_def)

lemma fst_EPerm''[simp]: "fst \<circ> Eperm'' \<sigma> = Pperm \<sigma> o fst"
unfolding fun_eq_iff by (simp add: Eperm''_def)


lemma triv_Eperm_lift: "(\<lambda>e p. e) \<circ> Eperm \<sigma> = lift Eperm \<sigma> o (\<lambda>e p. e)"
unfolding fun_eq_iff o_def lift_def by simp

lemma Eperm_inv_iff: "bij \<sigma> \<Longrightarrow> Eperm (inv \<sigma>) e1 = e \<longleftrightarrow> e1 = Eperm \<sigma> e"
sorry


(* This one OK, all sorries doable: *)
lemma dtorPermC: "dtorPermC Edtor' Eperm''"
unfolding dtorPermC_def apply clarify subgoal for \<sigma> p e
unfolding Eperm''_def unfolding Eperm'_Eperm 
apply(rule Ector_exhaust'[of e], simp)
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> apply safe 
    unfolding Eperm_Ector apply(subst Edtor'_\<phi>)
      subgoal using \<phi>_Gmap \<phi>_Gren by metis
      subgoal apply auto 
      apply(subst ctor0PermM[unfolded ctorPermM_def Eperm'_Eperm, rule_format])
        subgoal by (simp add: \<phi>_Gmap)
        subgoal by simp
        subgoal unfolding Gmap_comp Gmap_Gren unfolding lift_def o_def .. . .
     subgoal 
     apply(subgoal_tac "GVrs2 u \<inter> PVrs p = {} \<and> \<sigma> ` GVrs2 u \<inter> PVrs p = {}") 
        defer subgoal sorry (* OK *)
     unfolding Edtor'_not\<phi> apply safe 
     unfolding Eperm_Ector apply(subst Edtor'_not\<phi>)
      subgoal using \<phi>_Gmap \<phi>_Gren by metis
      subgoal apply simp  
      apply(subst Edtor1'_Ector)
        subgoal using \<phi>_Gmap \<phi>_Gren by metis
        subgoal unfolding GVrs2_Gmap GVrs2_Gren PVrs_Pperm  
          by (metis bij_is_inj image_Int image_empty)
        subgoal unfolding image_def apply auto apply(subst Edtor1'_Ector)
        apply auto subgoal for u0
        apply(rule exI[of _ "Gren (inv \<sigma>) (inv \<sigma>) u0"]) apply safe
          prefer 2 subgoal sorry (* OK *)
          subgoal 
          apply(rule exI[of _ "Gren (inv \<sigma>) (inv \<sigma>) (Gmap (Eperm'' (inv \<sigma>)) (Eperm'' (inv \<sigma>)) u0)"])
          apply safe
            subgoal unfolding Gmap_comp Gmap_Gren apply(subst Gmap_Gren)
              subgoal sorry (* OK *)
              subgoal sorry (* OK *)
              subgoal unfolding Gmap_comp apply simp 
              unfolding Gmap_o apply(subst o_def)
              apply(subst Eperm_Ector[symmetric])
                subgoal sorry (* OK *)
                subgoal sorry (* OK *)
                subgoal 
                unfolding Gmap_o[symmetric] triv_Eperm_lift unfolding Gmap_o
                unfolding o_def
                apply(subst (asm) ctor1PermM[unfolded ctorPermM_def, rule_format, unfolded Eperm'_Eperm, 
                            symmetric])
                  subgoal by (simp add: \<phi>_Gmap)
                  subgoal by simp
                  subgoal apply(subst Eperm_inv_iff) by auto . . .
              subgoal for e' unfolding GSupp1_Gmap apply auto subgoal for b apply(subst (asm) GSupp1_Gren)
                subgoal sorry (* OK*)
                subgoal sorry (* OK*)
                subgoal unfolding GSupp1_Gmap apply(auto simp: Eperm''_def) subgoal for pp ee 
                apply(subgoal_tac "pp = Pperm \<sigma> p")
                  subgoal apply auto sorry (* OK*)
                  subgoal by auto . . . .
              subgoal for pp unfolding GSupp2_Gmap apply auto apply(subst (asm) GSupp2_Gren)
                subgoal sorry (* OK*)
                subgoal sorry (* OK*)
                subgoal for ee unfolding GSupp2_Gmap apply(auto simp: Eperm''_def) subgoal for p' e'
                apply(subgoal_tac "p' = Pperm \<sigma> p")
                  subgoal apply auto sorry (* OK*)
                  subgoal by auto . . . 
              subgoal for a apply(subst (asm) GVrs2_Gren)
                subgoal sorry (* OK*) subgoal sorry (* OK*)
                subgoal unfolding GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap apply auto  subgoal for a
                apply(subgoal_tac "a \<in> \<sigma> ` PVrs p") 
                  subgoal by (metis IntI PVrs_Pperm empty_iff)
                  subgoal sorry (* OK *) . . .
             subgoal apply(subst Gmap_Gren[symmetric])
               subgoal sorry (* OK *) subgoal sorry (* OK *)
               subgoal unfolding Gmap_comp sorry (* OK *) . . . . . . . . .

lemma fst_single_Gmap: "fst ` GSupp1 u \<subseteq> {p} \<Longrightarrow> fst ` GSupp2 u \<subseteq> {p}
\<Longrightarrow> Gmap (\<lambda>(p',e). (p,e)) (\<lambda>(p',e). (p,e)) u = u"
apply(rule Gmap_cong_id) by auto

lemma fst_single_Gmap': 
assumes "fst ` GSupp1 u \<subseteq> {p}" "fst ` GSupp2 u \<subseteq> {p}"
shows "Gmap (Pair p) (Pair p) (Gmap snd snd u) = u"
apply(rule sym) apply(subst fst_single_Gmap[symmetric, of _ p])
  subgoal by fact subgoal by fact
  subgoal unfolding Gmap_comp o_def  
    by (meson Gmap_cong case_prod_beta) .

(* This one OK, all sorries doable: *)         
lemma dtorVrsGrenC: "dtorVrsGrenC Edtor' EVrs''"
unfolding dtorVrsGrenC_def EVrs'_EVrs EVrs''_def apply safe 
subgoal for p e U u1 u2   apply(rule Ector_exhaust'[of e]) apply safe
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi>  apply simp
    apply(subgoal_tac "GVrs2 u \<inter> PVrs p = {}") defer subgoal sorry (* OK *)
    unfolding Edtor1'_Ector apply auto 
    using Edtor_eq_imp[of "Gmap snd snd u1" "Gmap snd snd u2"]
    unfolding EVrs''_def EVrs'_EVrs apply auto subgoal for \<sigma> 
    apply(rule exI[of _ \<sigma>]) unfolding GVrs1_Gmap  GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap apply(intro conjI)
      subgoal . subgoal .
      subgoal apply(subgoal_tac "\<Union> {EVrs e |e. e \<in> snd ` GSupp1 u1} \<union> 
        \<Union> {EVrs e - GVrs2 u1 |e. e \<in> snd ` GSupp1 u1}  
    \<subseteq> \<Union> {EVrs b \<union> PVrs a |a b. (a, b) \<in> GSupp1 u1} \<union>
       \<Union> {EVrs b \<union> PVrs a - GVrs2 u1 |a b. (a, b) \<in> GSupp1 u1}")
         subgoal by (smt (verit, ccfv_threshold) Diff_iff Un_iff diff_shunt subsetI)
         subgoal by auto blast+ .  

 apply(subst (asm) Gmap_Gren[of id \<sigma>,symmetric]) subgoal sorry (* OK *) subgoal sorry (* OK *)
    subgoal sorry (* OK *) subgoal sorry (* OK *)
  apply(subst (asm) Gmap_Gren[of id \<sigma>,symmetric]) subgoal sorry (* OK *) subgoal sorry (* OK *)
    subgoal sorry (* OK *) subgoal sorry (* OK *)
    apply(subst fst_single_Gmap'[symmetric, of _ p]) 
      subgoal by auto subgoal by auto
      subgoal apply(subgoal_tac "Gmap (Pair p) (Pair p) (Gmap snd snd u2) = 
          Gmap (Pair p) (Pair p) (Gmap snd snd (Gren id \<sigma> u1))")
        subgoal unfolding Gmap_comp o_def id_def apply simp
        apply(rule Gmap_cong_id)
          subgoal apply(subst (asm) GSupp1_Gren) subgoal sorry (* OK *) subgoal sorry (* OK *)
            subgoal sorry (* OK *) subgoal sorry (* OK *)
            subgoal by auto .
          subgoal apply(subst (asm) GSupp2_Gren) subgoal sorry (* OK *) subgoal sorry (* OK *)
            subgoal sorry (* OK *) subgoal sorry (* OK *)
            subgoal by auto . .
        subgoal by simp . . . . . .


lemma tri_Un1: "A \<subseteq> B \<union> C \<Longrightarrow> A \<union> B \<subseteq> B \<union> C" by auto
lemma tri_Un3: "A \<union> A' \<union> A'' \<subseteq> B \<union> C \<Longrightarrow> B \<union> A \<union> A' \<union> A'' \<subseteq> B \<union> C" by auto


(* This one only works if we union with V *)
lemma Ector1'_Ector_EVrs: 
"\<not> \<phi> u \<Longrightarrow> EVrs'' (p, Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctor1VarsM[unfolded ctorVarsM_def EVrs'_EVrs, rule_format]])
  subgoal by (simp add: \<phi>_Gmap)
  subgoal apply(rule tri_Un3) unfolding EVrs'_EVrs EVrs_Ector GSupp1_Gmap GVrs1_Gmap by auto . 

lemma Ector0'_Ector_EVrs: 
"\<phi> u \<Longrightarrow> EVrs'' (p, Ector0' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctor0VarsM[unfolded ctorVarsM_def EVrs'_EVrs, rule_format]])
  subgoal by (simp add: \<phi>_Gmap)
  subgoal apply(rule tri_Un3) unfolding EVrs'_EVrs EVrs_Ector GSupp1_Gmap GVrs1_Gmap by auto . 

(* 
(* For Ector0' need to axiomatize the converse too. 
So in both cases, the symmetric difference is contained in V. Could go with this in 
an alternative axiomatization of Special_Model_Plus which does not go throgu Special_Model *)
lemma Ector0'_Ector_EVrs_rev: "\<phi> u \<Longrightarrow> EVrs (Ector u) \<subseteq> V \<union> EVrs (Ector0' u)"
sorry
*)

(* Needs to be an axiom: call that expression FreeVars u, and use it in the other axioms:  *)
lemma blah: "\<not> \<phi> u \<Longrightarrow> 
    GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 uu \<inter> PVrs p = {} \<Longrightarrow>
    Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p = Ector uu \<Longrightarrow>
    GVrs1 uu \<union> \<Union> {EVrs e' |e'. e' \<in> GSupp1 uu} \<union> \<Union> {EVrs e' - GVrs2 uu |e'. e' \<in> GSupp1 uu} \<subseteq> 
    GVrs1 u \<union> \<Union> {EVrs e' |e'. e' \<in> GSupp1 u} \<union> \<Union> {EVrs e' - GVrs2 u |e'. e' \<in> GSupp1 u} \<union> PVrs p"
sorry  (* This can replace one axiom for ECtor1' (since it makes it redundant *)

lemma dtorVrsC: "dtorVrsC Edtor' EVrs''"
unfolding EVrs'_EVrs EVrs''_def
unfolding dtorVrsC_def apply (intro allI) subgoal for pe apply(cases pe) subgoal for p e apply clarify
apply(rule Ector_exhaust'[of e]) apply clarify apply (intro conjI)
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi> 
    apply(subgoal_tac "GVrs2 u \<inter> PVrs p = {}") defer subgoal sorry (* OK *)
    unfolding Edtor1'_Ector unfolding EVrs_Ector GSupp1_Gmap GSupp2_Gmap apply clarsimp
    subgoal for ua 
    using blah[of u p "Gmap snd snd ua"] 
     unfolding EVrs''_def EVrs_Ector apply auto   
     apply (smt (z3) GVrs1_Gmap GVrs2_Gmap Un_iff Union_iff in_mono mem_Collect_eq)
     sorry . 


 using blah  apply auto 
    apply (smetis (lifting) EVrs''_def EVrs_Ector GVrs1_Gmap GVrs2_Gmap in_mono)
        sledgehammer
    apply (smt (verit,s ccfv_threshold) Diff_iff UnE Union_iff diff_shunt empty_iff mem_Collect_eq)
    by (smt (vesrit, ccfv_threshold) Diff_iff UnE Union_iff diff_shunt empty_iff mem_Collect_eq) .
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi>  
      using EVrs'_EVrs Ector0'_Ector_EVrs by blast 
    subgoal unfolding Edtor'_not\<phi> by simp . .
    

lemma nom: "nom Eperm' EVrs''"
unfolding nom_def apply safe
  subgoal for \<sigma>1 \<sigma>2 unfolding Eperm'_Eperm sorry
  subgoal for \<sigma>1 \<sigma>2 e unfolding Eperm'_Eperm EVrs''_def


end (* locale Special_Model *)






(****)




(* TODO: 
-- customize special_model
--- show that it gives rise to model
--- show that it gives rise to comodel
*)





 

end