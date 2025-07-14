theory Expression_Like
  imports "Binders.MRBNF_Recursor"
begin

(**************************)
(* 1. Preliminaries *)

declare supp_id_bound[simp] supp_inv_bound[simp] infinite_UNIV[simp]

definition "IImsupp' Inj Vr \<rho> = SSupp Inj \<rho> \<union> IImsupp Inj Vr \<rho>"

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

(**************************)
(* 2. The starting MN-monad / pre-(co)datatype *)

typedecl Gbd_type
consts Gbd :: "Gbd_type rel"

setup \<open>Sign.mandatory_path "G"\<close>
axiomatization where
  infinite_regular_card_order: "infinite_regular_card_order Gbd"
setup \<open>Sign.parent_path\<close>

class covar =
  assumes large: "cardSuc Gbd \<le>o |UNIV::'a set|"
    and regular: "regularCard |UNIV::'a set|"

class var =
  assumes large: "|Field Gbd| \<le>o |UNIV::'a set|"
    and regular: "regularCard |UNIV::'a set|"

instantiation Gbd_type :: var begin
instance apply standard
  apply simp
  by (meson G.infinite_regular_card_order card_of_unique
      card_order_on_Card_order infinite_regular_card_order_def
      regularCard_ordIso)
end

subclass (in covar) var
  apply standard
  apply (meson cardSuc_ordLess_ordLeq card_of_Card_order
      card_of_Field_ordIso G.infinite_regular_card_order
      infinite_regular_card_order.Card_order local.large
      ordIso_ordLeq_trans ordLeq_iff_ordLess_or_ordIso)
  by (rule local.regular)

subclass (in var) infinite
  apply standard
  using card_of_ordLeq_finite cinfinite_def
    G.infinite_regular_card_order
    infinite_regular_card_order.cinfinite local.large
  by auto

lemma large': "Gbd \<le>o |UNIV::'a::var set|"
  using Card_order_iff_ordLeq_card_of var_class.large
    G.infinite_regular_card_order infinite_regular_card_order.Card_order ordLeq_transitive
  by blast

lemma (in var) UN_bound: "|A| <o |UNIV::'a set| \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> |f x| <o |UNIV::'a set| )
  \<Longrightarrow> |\<Union>(f ` A)| <o |UNIV::'a set|"
  using card_of_Card_order card_of_UNION_ordLess_infinite_Field local.regular regularCard_stable
  by (metis Field_card_of infinite_UNIV)

lemma IImsupp_bound[simp]:
  "|SSupp Inj (\<rho> :: 'a::var \<Rightarrow> _)| <o |UNIV :: 'a set| \<Longrightarrow> (\<And>x. |Vr (\<rho> x)| <o |UNIV :: 'a set| ) \<Longrightarrow>
  |IImsupp' Inj (Vr :: _ \<Rightarrow> 'a set) \<rho>| <o |UNIV :: 'a set|"
  unfolding IImsupp_def IImsupp'_def
  by (auto simp: Un_bound UN_bound)

typedecl ('a1, 'a2, 'c1, 'c2) G
consts Gsub :: "('a1 :: var \<Rightarrow> 'a1) \<Rightarrow> ('a2 :: var \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G"
consts GVrs1 :: "('a1 :: var, 'a2 :: var, 'c1, 'c2) G \<Rightarrow> 'a1 set"
consts GVrs2 :: "('a1 :: var, 'a2 :: var, 'c1, 'c2) G \<Rightarrow> 'a2 set"
consts Gmap :: "('c1 \<Rightarrow> 'c1') \<Rightarrow> ('c2 \<Rightarrow> 'c2') \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1', 'c2') G"
consts GSupp1 :: "('a1 :: var, 'a2 :: var, 'c1, 'c2) G \<Rightarrow> 'c1 set"
consts GSupp2 :: "('a1 :: var, 'a2 :: var, 'c1, 'c2) G \<Rightarrow> 'c2 set"

setup \<open>Sign.mandatory_path "G"\<close>

axiomatization where
  Sb_Inj: "Gsub id id = id" and
  Sb_comp: "\<And>g1 g2 f1 f2.
       |supp (f1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       |supp (f2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow>
       |supp (g1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       |supp (g2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow>
       Gsub g1 g2 \<circ> Gsub f1 f2 = Gsub (g1 \<circ> f1) (g2 \<circ> f2)" and
  Vrs1_bd: "(\<And>x. |GVrs1 x| <o Gbd)" and
  Vrs2_bd: "(\<And>x. |GVrs2 x| <o Gbd)" and
  Vrs1_Sb: "(\<And>f1 f2 x.
       |supp (f1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       |supp (f2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow> GVrs1 (Gsub f1 f2 x) = f1 ` GVrs1 x)" and
  Vrs2_Sb: "(\<And>f1 f2 x.
       |supp (f1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       |supp (f2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow> GVrs2 (Gsub f1 f2 x) = f2 ` GVrs2 x)" and
  Sb_cong: "\<And>f1 f2 g1 g2 x.
       |supp (f1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       |supp (f2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow>
       |supp (g1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       |supp (g2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow>
       (\<And>a1. a1 \<in> GVrs1 x \<Longrightarrow> f1 a1 = g1 a1) \<Longrightarrow>
       (\<And>a2. a2 \<in> GVrs2 x \<Longrightarrow> f2 a2 = g2 a2) \<Longrightarrow>
       Gsub f1 f2 x = Gsub g1 g2 x" and
  Map_id: "Gmap id id = id" and
  Map_comp: "\<And>f1 f2 g1 g2. Gmap g1 g2 \<circ> Gmap f1 f2 = Gmap (g1 \<circ> f1) (g2 \<circ> f2)" and
  Supp1_Map: "(\<And>f1 f2 x. GSupp1 (Gmap f1 f2 x) = f1 ` GSupp1 x)" and
  Supp2_Map: "(\<And>f1 f2 x. GSupp2 (Gmap f1 f2 x) = f2 ` GSupp2 x)" and
  Supp1_bd: "(\<And>x. |GSupp1 x| <o Gbd)" and
  Supp2_bd:  "(\<And>x. |GSupp2 x| <o Gbd)" and
  Map_cong: "\<And>f1 f2 g1 g2 x.
        (\<And>a. a \<in> GSupp1 x \<Longrightarrow> f1 a = g1 a) \<Longrightarrow>
        (\<And>a. a \<in> GSupp2 x \<Longrightarrow> f2 a = g2 a) \<Longrightarrow>
        Gmap f1 f2 x = Gmap g1 g2 x" and
  Map_Sb: "\<And>f1 f2 g1 g2.
        |supp (g1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
        |supp (g2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow>
        Gmap f1 f2 \<circ> Gsub g1 g2 = Gsub g1 g2 \<circ> Gmap f1 f2" and
  Supp1_Sb: "(\<And>g1 g2 x.
        |supp (g1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
        |supp (g2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow> GSupp1 (Gsub g1 g2 x) = GSupp1 x)" and
  Supp2_Sb:"(\<And>g1 g2 x.
        |supp (g1 :: 'a1::var \<Rightarrow> 'a1)| <o |UNIV :: 'a1 set| \<Longrightarrow>
        |supp (g2 :: 'a2::var \<Rightarrow> 'a2)| <o |UNIV :: 'a2 set| \<Longrightarrow> GSupp2 (Gsub g1 g2 x) = GSupp2 x)" and
  Vrs_Map1: "(\<And>f1 f2 x. GVrs1 (Gmap f1 f2 x) = GVrs1 x)" and
  Vrs_Map2: "(\<And>f1 f2 x. GVrs2 (Gmap f1 f2 x) = GVrs2 x)"

lemmas Vrs_Sb = G.Vrs1_Sb G.Vrs2_Sb
lemmas Vrs_bd = G.Vrs1_bd G.Vrs2_bd
lemmas Supp_Map = G.Supp1_Map G.Supp2_Map
lemmas Supp_bd = G.Supp1_bd G.Supp2_bd
lemmas Supp_Sb = G.Supp1_Sb G.Supp2_Sb
lemmas Vrs_Map = G.Vrs_Map1 G.Vrs_Map2

setup \<open>Sign.parent_path\<close>

(* In this case the flat version, Gren, happens to be the same as Gsub. *)
definition Gren :: 
  "('a1 :: var \<Rightarrow> 'a1) \<Rightarrow> ('a2 :: var \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G" where 
  "Gren \<rho>1 \<rho>2 u = Gsub \<rho>1 \<rho>2 u"

lemma GVrs2_bound[simp]: "|GVrs2 (u::('a :: var, 'a, 'e, 'e) G)| <o |UNIV :: 'a set|"
  by (rule ordLess_ordLeq_trans[OF G.Vrs_bd(2) large'])


(**************************)
(* 3. Generalized Nominal Assumptions *)

locale Nominal = 
  fixes Eperm :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> 'e \<Rightarrow> 'e"
  and EVrs :: "'e \<Rightarrow> 'a set"
  and Ebd :: "'bd rel"
  assumes
  Eperm_comp:
  "\<And>\<sigma> \<tau>. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   Eperm \<sigma> o Eperm \<tau> = Eperm (\<sigma> o \<tau>)"
  and Eperm_cong_id:
  "\<And>\<sigma> e. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma> a = a) \<Longrightarrow> Eperm \<sigma> e = e"
  and Ebd_infinite_regular_card_order: "infinite_regular_card_order Ebd"
  and Ebd_le: "Ebd \<le>o |UNIV :: 'a::var set|"
  and EVrs_bd:
  "\<And>x. |EVrs (x :: 'e)| <o Ebd"
begin

lemma Eperm_id: "Eperm id = id"
  apply (rule ext)
  apply (rule trans[OF Eperm_cong_id id_apply[symmetric]])
    apply simp_all
  done

lemma EVrs_bound[simp]: "|EVrs (x :: 'e)| <o |UNIV :: 'a set|"
  by (rule ordLess_ordLeq_trans[OF EVrs_bd Ebd_le])

end

(* relativized nominal :*)
locale NominalRel = 
  fixes Pvalid :: "'e \<Rightarrow> bool"
  and Pperm :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> 'e \<Rightarrow> 'e"
  and PVrs :: "'e \<Rightarrow> 'a set"
  assumes
  Eperm_Evalid: "\<And>\<sigma> e. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> Pvalid e \<Longrightarrow> Pvalid (Pperm \<sigma> e)"
  and Eperm_comp:
  "\<And>\<sigma> \<tau> e. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   Pvalid e \<Longrightarrow>
   Pperm \<sigma> (Pperm \<tau> e) = Pperm (\<sigma> o \<tau>) e"
  and Eperm_cong_id:
  "\<And>\<sigma> e. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> Pvalid e \<Longrightarrow>
   (\<And>a. a \<in> PVrs e \<Longrightarrow> \<sigma> a = a) \<Longrightarrow> Pperm \<sigma> e = e" 


(**************************)
(* 4. Expression-Like Entities *)

locale Expression = Nominal +
  fixes Ector :: "('a :: var, 'a, 'e, 'e) G \<Rightarrow> 'e"
  assumes EVrs_Eperm:
  "\<And>\<sigma> u. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> 
   EVrs (Eperm \<sigma> u) \<subseteq> \<sigma> ` EVrs u"
  and Eperm_Ector:
  "\<And>\<sigma> u. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
    Eperm \<sigma> (Ector u) = Ector (Gren \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u))"
  and EVrs_Ector:
  "\<And>u. EVrs (Ector u) =
     GVrs1 u \<union> ((\<Union>e \<in> GSupp1 u. EVrs e) - GVrs2 u) \<union> (\<Union>e \<in> GSupp2 u. EVrs e)"
  and Ector_inject: "\<And>x y. Ector x = Ector y \<longleftrightarrow>
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
begin

lemma Eperm_cong: "bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
         bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma> a = \<tau> a) \<Longrightarrow> Eperm \<sigma> e = Eperm \<tau> e"
  apply (rule trans[OF _ Eperm_cong_id, of _ "\<sigma> o inv \<tau>"])
     apply (auto simp: Eperm_comp[THEN fun_cong, simplified] supp_comp_bound
      dest: EVrs_Eperm[THEN set_mp, rotated -1] simp flip: o_assoc)
  done

lemma Ector_fresh_inject:
  assumes "GVrs2 x \<inter> A = {}" "GVrs2 y \<inter> A = {}" "|A :: 'a::var set| <o |UNIV :: 'a set|"
  shows "(Ector x = Ector y) \<longleftrightarrow> (\<exists>\<sigma>. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and> imsupp \<sigma> \<inter> A = {}
    \<and> id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  apply (subst Ector_inject; rule iffI; (elim exE conjE)?)
  subgoal for \<sigma>
    apply (insert ex_avoiding_bij[of \<sigma> "(\<Union> (EVrs ` GSupp1 x) - GVrs2 x)" "GVrs2 x" A])
    apply (drule meta_mp; simp add: UN_bound card_of_minus_bound ordLess_ordLeq_trans[OF G.Supp_bd(1) large'] ordLess_ordLeq_trans[OF G.Vrs_bd(2) large'] assms)+
    apply (elim exE conjE)
    subgoal for \<tau>
      apply (auto simp: G.Vrs_Map Gren_def intro!: exI[of _ \<tau>] trans[OF G.Sb_cong arg_cong[where f="Gsub _ _", OF G.Map_cong]] Eperm_cong)
      using G.Vrs_Map(2) G.Vrs_Sb(2) assms(2) imageI supp_id_bound apply blast
      apply (smt (verit, ccfv_threshold) Diff_iff G.Vrs_Map(2) G.Vrs_Sb(2) UN_I assms(2) disjoint_iff_not_equal id_on_eq imageI supp_id_bound)
      done
    done
  apply blast
  done



end

end