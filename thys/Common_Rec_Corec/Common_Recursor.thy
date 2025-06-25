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

lemma Gmap_comp: "Gmap f1 f2 (Gmap g1 g2 u) = Gmap (f1 o g1) (f2 o g2) u"
unfolding Gmap_o by simp

lemma Gmap_id'[simp]: "Gmap (\<lambda>x. x) (\<lambda>x. x) = id"
using Gmap_id unfolding id_def .

typedecl E

consts Ector :: "(E,E) G \<Rightarrow> E"
consts Eperm :: "(var \<Rightarrow> var) \<Rightarrow> E \<Rightarrow> E"
consts EVrs :: "E \<Rightarrow> var set"

definition Edtor :: "E \<Rightarrow> ((E,E) G) set" where 
"Edtor e = {u . Ector u = e}"


(* *)
type_synonym E' = E 


definition dtorNeC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> bool" where 
"dtorNeC dtor \<equiv> \<forall>e U. dtor e = Inl U \<longrightarrow> U \<noteq> {}"

definition dtorPermC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> bool" 
where "dtorPermC dtor perm \<equiv> 
\<forall>\<sigma> e. small \<sigma> \<and> bij \<sigma> \<and> 
  (\<forall> U. dtor e = Inl U \<longrightarrow> (\<exists>U'. dtor (perm \<sigma> e) = Inl U' \<and> U' \<subseteq> Gren \<sigma> \<sigma> ` U))
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
  (\<forall>e1. dtor e = Inr e1 \<longrightarrow> Vrs e \<subseteq> EVrs e1)
)"

(* Full-recursion comodel: I keep E' as an abbreviation for E to avoid confusion: *)
locale Comodel =
fixes (* no set V, as we need no Barendregt convention here *)
Edtor' :: "E' \<Rightarrow> ((E',E')G) set + E" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' :: "E' \<Rightarrow> var set" 
begin 

definition comodel :: bool
where 
"comodel \<equiv> 
nom Eperm' EVrs' 
\<and>
dtorNeC Edtor' 
\<and>
dtorPermC Edtor' Eperm' 
\<and>
dtorVrsGrenC Edtor' EVrs'
\<and>
dtorVrsC Edtor' EVrs'"


definition corec :: "E \<Rightarrow> E'" where 
"corec = undefined"

lemma corec_Edtor_Inl:
assumes "comodel"
shows "Edtor' e = Inl U \<Longrightarrow> Gmap corec corec ` U  \<subseteq> Edtor (corec e)"
sorry

lemma corec_Edtor_Inr:
assumes "comodel"
shows "Edtor' e = Inr e1 \<Longrightarrow> corec e = e1"
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

lemma corec_unique: (* to double check if we have this *)
assumes "comodel"
assumes "\<And> e U. Edtor' e = Inl U \<Longrightarrow> Gmap H H ` U  \<subseteq> Edtor (corec e)"
and "\<And>e e1. Edtor' e = Inr e1 \<Longrightarrow> H e = e1"
shows "H = corec"
sorry

end (* locale Comodel *)


(****)
(* Full-recursion Barendregt-enriched model, but for codomain equal to E; 
I keep E' as an abbreviation to avoid confusion. *)

definition ctorPermM :: "var set \<Rightarrow> (('E' \<times> E,'E' \<times> E) G \<Rightarrow> 'E') \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') 
\<Rightarrow> bool" where 
"ctorPermM V ctor perm \<equiv> 
(\<forall>u'u \<sigma>. small \<sigma> \<and> bij \<sigma> \<and> supp \<sigma> \<inter> V = {} \<longrightarrow> 
       perm \<sigma> (ctor u'u) = 
       ctor (Gmap (map_prod (perm \<sigma>) (Eperm \<sigma>)) (map_prod (perm \<sigma>) (Eperm \<sigma>)) u'u))"

definition ctorVarsM :: "var set \<Rightarrow> (('E' \<times> E,'E' \<times> E) G \<Rightarrow> 'E') \<Rightarrow> ('E' \<Rightarrow> var set)
\<Rightarrow> bool" where 
"ctorVarsM V ctor Vrs \<equiv> (\<forall>u'u. Vrs (ctor u'u) - V \<subseteq> 
     GVrs1 u'u \<union> 
     (\<Union> {Vrs e' \<union> EVrs e | e' e . (e',e) \<in> GSupp1 u'u}) \<union> 
     (\<Union> {Vrs e' \<union> EVrs e - GVrs2 u'u | e' e . (e',e) \<in> GSupp1 u'u}) 
)"

locale Model =
fixes V :: "var set" 
 (* "\<times> E" is the full-recursion bit in addition to iteration *)
and Ector' :: "(E' \<times> E,E' \<times> E) G \<Rightarrow> E'" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' ::"E' \<Rightarrow> var set" 
assumes nom: "nom Eperm' EVrs'"
and ctorPermM: "ctorPermM V Ector' Eperm'"
and ctorVarsM: "ctorVarsM V Ector' EVrs'"
begin 


definition rec :: "E \<Rightarrow> E'" where 
"rec = undefined"

lemma rec_Ector:
assumes "countable V" 
shows "GVrs2 u \<inter> V = {} \<Longrightarrow>  
 rec (Ector u) = 
 Ector' (Gmap (\<lambda>e. (rec  e, e)) (\<lambda>e. (rec e, e)) u)"
sorry

lemma rec_Eperm:
assumes "countable V"  
shows "small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> supp \<sigma> \<inter> V = {} \<Longrightarrow> 
 rec (Eperm \<sigma> e) = Eperm' \<sigma> (rec  e)"
sorry

lemma rec_EVrs:
assumes "countable V"  
shows "EVrs' (rec e) - V \<subseteq> EVrs e"
sorry


lemma rec_unique:
assumes "countable V" 
assumes "\<And>u. GVrs2 u \<inter> V = {} \<Longrightarrow>
 H (Ector u) = 
 Ector' (Gmap (\<lambda>e. (H  e, e)) (\<lambda>e. (H e, e)) u)"
shows "H = rec" 
sorry

end (* locale Model *)

(******)


consts \<phi> :: "('e,'e) G \<Rightarrow> bool"
axiomatization where \<phi>_Gmap: "\<And> u f g. \<phi> (Gmap f g u) \<longleftrightarrow> \<phi> u"

definition ctor0PermM :: "var set \<Rightarrow> ((E,E) G \<Rightarrow> 'E') \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') 
 \<Rightarrow> bool" where 
"ctor0PermM V ctor0 perm \<equiv> 
(\<forall>u \<sigma>. \<phi> u \<and> 
       small \<sigma> \<and> bij \<sigma> \<and> supp \<sigma> \<inter> V = {} \<longrightarrow> 
       perm \<sigma> (ctor0 u) = 
       ctor0 (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u))"

definition ctor1PermM :: "var set \<Rightarrow> (('E','E') G \<Rightarrow> 'E') \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') 
 \<Rightarrow> bool" where 
"ctor1PermM V ctor1 perm \<equiv> 
(\<forall>u' \<sigma>. \<not> \<phi> u' \<and> 
       small \<sigma> \<and> bij \<sigma> \<and> supp \<sigma> \<inter> V = {} \<longrightarrow> 
       perm \<sigma> (ctor1 u') = 
       ctor1 (Gmap (perm \<sigma>) (perm \<sigma>) u'))"

definition ctor0VarsM :: "var set \<Rightarrow> ((E,E) G \<Rightarrow> 'E') \<Rightarrow> ('E' \<Rightarrow> var set)
\<Rightarrow> bool" where 
"ctor0VarsM V ctor Vrs \<equiv> 
 \<forall>u. \<phi> u \<longrightarrow> 
     Vrs (ctor u) - V \<subseteq> 
     GVrs1 u \<union> 
     (\<Union> {EVrs e | e . e \<in> GSupp1 u}) \<union> 
     (\<Union> {EVrs e - GVrs2 u | e . e \<in> GSupp1 u})"

definition ctor1VarsM :: "var set \<Rightarrow> (('E','E') G \<Rightarrow> 'E') \<Rightarrow> ('E' \<Rightarrow> var set)
\<Rightarrow> bool" where 
"ctor1VarsM V ctor Vrs \<equiv>  
 \<forall>u. \<not> \<phi> u \<longrightarrow> 
     Vrs (ctor u) - V \<subseteq> 
     GVrs1 u \<union> 
     (\<Union> {Vrs e' | e' . e' \<in> GSupp1 u}) \<union> 
     (\<Union> {Vrs e' - GVrs2 u | e' . e' \<in> GSupp1 u})"

locale Special_Model = 
fixes 
Ector0' :: "(E,E) G \<Rightarrow> E'" 
and Ector1' :: "(E',E') G \<Rightarrow> E'" 
assumes nom: "nom Eperm' EVrs'"
and ctor0PermM: "ctor0PermM V Ector0' Eperm'" and 
    ctor1PermM: "ctor1PermM V Ector1' Eperm'"
and ctor0VarsM: "ctor0VarsM V Ector0' EVrs'" and 
    ctor1VarsM: "ctor1VarsM V Ector1' EVrs'"
begin

(* 1. Recursion principle by associating a model to a special-model: *)

definition Ector' :: "(E' \<times> E,E' \<times> E) G \<Rightarrow> E'" where 
"Ector' u'u \<equiv> if \<phi> u'u then Ector0' (Gmap snd snd u'u) else Ector1' (Gmap fst fst u'u)"

lemma Ector'_\<phi>[simp]: "\<phi> u'u \<Longrightarrow> Ector' u'u = Ector0' (Gmap snd snd u'u)"
unfolding Ector'_def by auto

lemma Ector'_not\<phi>[simp]: "\<not> \<phi> u'u \<Longrightarrow> Ector' u'u =Ector1' (Gmap fst fst u'u)"
unfolding Ector'_def by auto

lemma ctorPermM: "ctorPermM V Ector' Eperm'"
unfolding ctorPermM_def apply safe
  subgoal for u'u \<sigma> apply(cases "\<phi> u'u")
    subgoal unfolding Ector'_\<phi>  
    apply(subst ctor0PermM[unfolded ctor0PermM_def, rule_format, 
      where V = V and Eperm' = Eperm' and \<sigma> = \<sigma>])
      subgoal using \<phi>_Gmap by auto
      subgoal apply(subst Ector'_\<phi> )
        subgoal using \<phi>_Gmap by auto
        subgoal unfolding Gmap_comp unfolding o_def by simp . .
    subgoal unfolding Ector'_not\<phi>  
    apply(subst ctor1PermM[unfolded ctor1PermM_def, rule_format, 
      where V = V and Eperm' = Eperm' and \<sigma> = \<sigma>])
      subgoal using \<phi>_Gmap by auto
      subgoal apply(subst Ector'_not\<phi> )
        subgoal using \<phi>_Gmap by auto
        subgoal unfolding Gmap_comp unfolding o_def by simp . . . .

lemma ctorVarsM: "ctorVarsM V Ector' EVrs'"
unfolding ctorVarsM_def apply(intro allI)
  subgoal for u'u apply(cases "\<phi> u'u")
    subgoal unfolding Ector'_\<phi>   
    apply(rule subset_trans[OF ctor0VarsM[unfolded ctor0VarsM_def, rule_format, 
      where V = V]]) 
      subgoal using \<phi>_Gmap by auto
      subgoal unfolding GSupp1_Gmap GSupp2_Gmap GVrs1_Gmap GVrs2_Gmap  
      by auto blast+ .
    subgoal unfolding Ector'_not\<phi>   
    apply(rule subset_trans[OF ctor1VarsM[unfolded ctor1VarsM_def, rule_format, 
      where V = V]]) 
      subgoal using \<phi>_Gmap by auto
      subgoal unfolding GSupp1_Gmap GSupp2_Gmap GVrs1_Gmap GVrs2_Gmap  
      by auto blast+ . . .


(* specia models form models: *)
sublocale Model where Ector' = Ector' and Eperm' = Eperm' and EVrs' = EVrs 
apply standard 
using nom ctorPermM ctorVarsM by auto 


(* and now we customize their recursion theorems: *)
thm rec_Ector rec_Eperm rec_unique 
(* NB: these stay the same: *) thm rec_EVrs rec_unique

 
lemma rec_Ector_\<phi>:
assumes "\<phi> u" and "countable V"  
shows "GVrs2 u \<inter> V = {} \<Longrightarrow> rec (Ector u) = Ector0' u"
apply(subst rec_Ector[where V = V])
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms apply(subst Ector'_\<phi>)
    subgoal using \<phi>_Gmap by auto
    subgoal unfolding Gmap_comp unfolding o_def by simp . .

lemma rec_Ector_not_\<phi>:
assumes "\<not> \<phi> u" and "countable V" 
shows "GVrs2 u \<inter> V = {} \<Longrightarrow> rec (Ector u) = Ector1' (Gmap rec rec u)"
apply(subst rec_Ector[where V = V])
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms apply(subst Ector'_not\<phi>)
    subgoal using \<phi>_Gmap by auto
    subgoal unfolding Gmap_comp unfolding o_def by simp . .

lemma rec_unique':
assumes "countable V" 
assumes "\<And>u. GVrs2 u \<inter> V = {} \<Longrightarrow>
 (\<phi> u \<longrightarrow> H (Ector u) = Ector0' u)
 \<and>
 (\<not> \<phi> u \<longrightarrow> H (Ector u) = Ector1' (Gmap H H u))"
shows "H = rec" 
sorry


(* 2. Corecursion principle by associating a comodel to a special-model: *)

end (* locale Special_Model *)






(****)




(* TODO: 
-- customize special_model
--- show that it gives rise to model
--- show that it gives rise to comodel
*)





 

end