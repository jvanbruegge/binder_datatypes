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
Gmap_o: "\<And>f1 f2 g1 g2. Gmap (f1 o f2) (g1 o g2) = Gmap f1 g1 o Gmap f2 g2"

lemma Gmap_comp: "Gmap f1 g1 (Gmap f2 g2 u) = Gmap (f1 o f2) (g1 o g2) u"
unfolding Gmap_o by simp

lemma Gmap_id'[simp]: "Gmap (\<lambda>x. x) (\<lambda>x. x) = id"
using Gmap_id unfolding id_def .

typedecl E

consts Ector :: "(E,E) G \<Rightarrow> E"
consts Eperm :: "(var \<Rightarrow> var) \<Rightarrow> E \<Rightarrow> E"
consts EVrs :: "E \<Rightarrow> var set"

definition Edtor :: "E \<Rightarrow> ((E,E) G) set" where 
"Edtor e = {u . Ector u = e}"

(* Full-recursion Barendregt-enriched model, but for codomain equal to E; 
I keep E' as an abbreviation to avoid confusion. *)
type_synonym E' = E 

locale Model =
fixes V :: "var set" 
 (* "\<times> E" is the full-recursion bit in addition to iteration *)
and Ector' :: "(E' \<times> E,E' \<times> E) G \<Rightarrow> E'" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' ::"E' \<Rightarrow> var set" 
begin 

definition model :: bool
where 
"model \<equiv> 
(\<forall>\<sigma>1 \<sigma>2. small \<sigma>1 \<and> bij \<sigma>1 \<and> small \<sigma>2 \<and> bij \<sigma>2 \<longrightarrow>  
 Eperm' (\<sigma>1 o \<sigma>2) = Eperm' \<sigma>1 o Eperm' \<sigma>2)
\<and>
(\<forall>\<sigma>1 \<sigma>2 e'. 
  small \<sigma>1 \<and> bij \<sigma>1 \<and> small \<sigma>2 \<and> bij \<sigma>2 \<and>  
  (\<forall>a\<in>EVrs' e'. \<sigma>1 a = \<sigma>2 a) \<longrightarrow> 
  Eperm' \<sigma>1 e' = Eperm' \<sigma>2 e')
\<and>
(\<forall>u'u \<sigma>. small \<sigma> \<and> bij \<sigma> \<and> supp \<sigma> \<inter> V = {} \<longrightarrow> 
       Eperm' \<sigma> (Ector' u'u) = 
       Ector' (Gmap (map_prod (Eperm' \<sigma>) (Eperm \<sigma>)) (map_prod (Eperm' \<sigma>) (Eperm \<sigma>)) u'u))
\<and>
(\<forall>u'u. EVrs' (Ector' u'u) - V \<subseteq> 
     GVrs1 u'u \<union> 
     (\<Union> {EVrs' e' \<union> EVrs e | e' e . (e',e) \<in> GSupp1 u'u}) \<union> 
     (\<Union> {EVrs' e' \<union> EVrs e - GVrs2 u'u | e' e . (e',e) \<in> GSupp1 u'u}) 
)"


definition rec :: "E \<Rightarrow> E'" where 
"rec = undefined"

lemma rec_Ector:
assumes "countable V" and "model"
shows "GVrs2 u \<inter> V = {} \<Longrightarrow>  
 rec (Ector u) = 
 Ector' (Gmap (\<lambda>e. (rec  e, e)) (\<lambda>e. (rec e, e)) u)"
sorry

lemma rec_Eperm:
assumes "countable V" and "model"
shows "small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> supp \<sigma> \<inter> V = {} \<Longrightarrow> 
 rec (Eperm \<sigma> e) = Eperm' \<sigma> (rec  e)"
sorry

lemma rec_EVrs:
assumes "countable V" and "model"
shows "EVrs' (rec e) - V \<subseteq> EVrs e"
sorry

end (* locale Model *)


locale Special_Model = Model + 
fixes \<phi> :: "(E' \<times> E,E' \<times> E) G \<Rightarrow> bool"
and Ector'' :: "(E,E) G \<Rightarrow> E'" 
assumes 
\<phi>_Ector'_Ector'': 
"\<And>u'u. \<phi> u'u \<Longrightarrow> Ector' u'u = Ector'' (Gmap snd snd u'u)"
and 
not_\<phi>_Ector'_Ector: 
"\<And>u'u. \<not> \<phi> u'u \<Longrightarrow> Ector' u'u = Ector (Gmap fst fst u'u)"
(* Probably will also be needed: this \<phi> case: has no bound variables, 
and no recursive components, i.e., is a base case
and 
"\<And>u'u. \<phi> u'u \<Longrightarrow> GVrs2 u'u = {}  \<and> GSupp2 u'u = {} \<and> GSupp1 u'u = {}"
*)
(* will probably also need some equivariance of \<phi>: to phrase the model conditions 
as conditions on \<phi> and Ector'' instead of Ector'
*)
begin


lemma rec_Ector_\<phi>:
assumes "\<phi> (Gmap (\<lambda>e. (rec  e, e)) (\<lambda>e. (rec e, e)) u)" 
and "countable V" and "model"
shows "GVrs2 u \<inter> V = {} \<Longrightarrow>  
 rec (Ector u) = Ector'' u"
apply(subst rec_Ector)
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal apply(subst \<phi>_Ector'_Ector'')
    subgoal using assms by simp
    subgoal apply(subst Gmap_comp) unfolding o_def by simp . .

lemma rec_Ector_not_\<phi>:
assumes "\<not> \<phi> (Gmap (\<lambda>e. (rec  e, e)) (\<lambda>e. (rec e, e)) u)" 
and "countable V" and "model"
shows "GVrs2 u \<inter> V = {} \<Longrightarrow>  
 rec (Ector u) = Ector (Gmap rec rec u)"
apply(subst rec_Ector)
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal apply(subst not_\<phi>_Ector'_Ector)
    subgoal using assms by simp
    subgoal apply(subst Gmap_comp) unfolding o_def by simp . .

end (* locale Special_Model *)



(****)

locale Comodel =
fixes (* no set V, as we need no Barendregt convention here *)
Edtor' :: "E' \<Rightarrow> ((E',E')G) set + E'" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' :: "E' \<Rightarrow> var set" 
begin 

definition comodel :: bool
where 
"comodel \<equiv> 
(\<forall>\<sigma>1 \<sigma>2. small \<sigma>1 \<and> bij \<sigma>1 \<and> small \<sigma>2 \<and> bij \<sigma>2 \<longrightarrow>  
 Eperm' (\<sigma>1 o \<sigma>2) = Eperm' \<sigma>1 o Eperm' \<sigma>2)
\<and>
(\<forall>\<sigma>1 \<sigma>2 e'. 
  small \<sigma>1 \<and> bij \<sigma>1 \<and> small \<sigma>2 \<and> bij \<sigma>2 \<and>  
  (\<forall>a\<in>EVrs' e'. \<sigma>1 a = \<sigma>2 a) \<longrightarrow> 
  Eperm' \<sigma>1 e' = Eperm' \<sigma>2 e')
\<and>
(\<forall>e U. Edtor' e = Inl U \<longrightarrow> U \<noteq> {})
\<and>
(\<forall>e U u1 u2. Edtor' e = Inl U \<and> {u1,u2} \<subseteq> U \<longrightarrow> 
   (\<exists>\<sigma>. small \<sigma> \<and> bij \<sigma> \<and> 
        supp \<sigma> \<subseteq> GVrs1 u1 \<union> 
                 (\<Union> {EVrs' e | e . e \<in> GSupp1 u1}) \<union> 
                 (\<Union> {EVrs' e - GVrs2 u1 | e . e \<in> GSupp1 u1}) \<and> 
        u2 = Gren id \<sigma> u1)) 
\<and>
(\<forall>e u U. Edtor' e = Inl U \<and> u \<in> U \<longrightarrow> 
  GVrs1 u \<union> 
  (\<Union> {EVrs' e | e . e \<in> GSupp1 u}) \<union> 
  (\<Union> {EVrs' e - GVrs2 u | e . e \<in> GSupp1 u}) 
  \<subseteq> 
  EVrs' e)"




definition corec :: "E \<Rightarrow> E'" where 
"corec = undefined"

lemma corec_Edtor_Inl:
assumes "comodel"
shows "Edtor' e' = Inl U' \<Longrightarrow> Gmap corec corec ` U  \<subseteq> Edtor (corec e')"
sorry

lemma corec_Edtor_Inr:
assumes "comodel"
shows "Edtor' e' = Inr e1' \<Longrightarrow> corec e' = e1'"
sorry

lemma corec_Eperm:
assumes "comodel"
shows "small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> supp \<sigma> \<inter> V = {} \<Longrightarrow> 
 corec (Eperm' \<sigma> e') = Eperm \<sigma> (corec e')"
sorry

lemma rec_EVrs:
assumes "comodel"
shows "EVrs' e' \<subseteq> EVrs (corec e')"
sorry

end (* locale Comodel *)


(* TODO: 
-- customize special_model
--- show that it gives rise to model
--- show that it gives rise to comodel
*)





 

end