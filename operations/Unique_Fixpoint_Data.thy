theory Unique_Fixpoint_Data
  imports "Binders.MRBNF_Recursor" "../operations/BMV_Monad"
begin

declare supp_id_bound[simp] supp_inv_bound[simp] infinite_UNIV[simp]

definition "IImsupp' Inj Vr \<rho> = SSupp Inj \<rho> \<union> IImsupp Inj Vr \<rho>"

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

typedecl ('a1, 'a2, 'x1, 'x2) G
consts Gsub :: "('a1 :: var \<Rightarrow> 'a1) \<Rightarrow> ('a2 :: var \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G"
consts GVrs1 :: "('a1 :: var, 'a2 :: var, 'x1, 'x2) G \<Rightarrow> 'a1 set"
consts GVrs2 :: "('a1 :: var, 'a2 :: var, 'x1, 'x2) G \<Rightarrow> 'a2 set"
consts Gmap :: "('x1 \<Rightarrow> 'x1') \<Rightarrow> ('x2 \<Rightarrow> 'x2') \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G \<Rightarrow> ('a1, 'a2, 'x1', 'x2') G"
consts GSupp1 :: "('a1 :: var, 'a2 :: var, 'x1, 'x2) G \<Rightarrow> 'x1 set"
consts GSupp2 :: "('a1 :: var, 'a2 :: var, 'x1, 'x2) G \<Rightarrow> 'x2 set"
consts Gwit :: "('a1, 'a2, 'x1, 'x2) G"

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

definition "GMAP = (\<lambda>\<rho>1 \<rho>2 f1 f2 x. Gren \<rho>1 \<rho>2 (Gmap f1 f2 x))"

declare [[typedef_overloaded]]
mrbnf "('a1::var, 'a2::var, 'x1, 'x2) G"
  map: GMAP
  sets: free: GVrs1 bound: GVrs2 live: GSupp1 live: GSupp2
  bd: Gbd
  wits: Gwit
  var_class: var
  sorry
print_theorems

consts \<eta> :: "'a1 :: var \<Rightarrow> ('a1, 'a2 :: var, 'x1, 'x2) G"
consts \<eta>' :: "'a1 :: var \<Rightarrow> ('a1, 'a2 :: var, 'x1, 'x2) G"

axiomatization where
  eta_inversion: "\<And>\<delta>1 \<delta>2 f1 f2 u a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 u) = (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G) \<Longrightarrow> \<exists>y. u = \<eta> y"
  and eta_natural: "\<And>\<delta>1 \<delta>2 f1 f2 a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)) = \<eta> (\<delta>1 a)"
  and eta_mem: "\<And>a. a \<in> GVrs1 (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)"
  and eta'_inversion: "\<And>\<delta>1 \<delta>2 f1 f2 u a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 u) = \<eta>' a \<Longrightarrow> \<exists>y. u = \<eta>' y"
  and eta'_natural: "\<And>\<delta>1 \<delta>2 f1 f2 a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta>' a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)) = \<eta>' (\<delta>1 a)"
  and eta'_mem: "\<And>a. a \<in> GVrs1 (\<eta>' a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)"
  and eta_inj: "\<And>a a'. \<eta> a = \<eta> a' \<Longrightarrow> a = a'"
  and eta'_inj: "\<And>a a'. \<eta>' a = \<eta>' a' \<Longrightarrow> a = a'"
  and eta_distinct: "\<And>a a'. \<eta> a \<noteq> \<eta>' a'"

lemma eta_inject: "\<eta> a = \<eta> a' \<longleftrightarrow> a = a'"
  using eta_inj by metis
lemma eta'_inject: "\<eta>' a = \<eta>' a' \<longleftrightarrow> a = a'"
  using eta'_inj by metis

lemma eta_distinct': "\<eta>' a \<noteq> \<eta> a'"
  using eta_distinct[of a' a] by metis

lemma GVrs_eta[simp]:
  "GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {a}"
  "GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b assume b: "b \<in> GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  { assume "a \<noteq> b"
    then have *: "\<eta> a = Gsub (b \<leftrightarrow> c) id (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using eta_natural[of "b \<leftrightarrow> c" id id id a, symmetric, simplified] that
      by (auto simp: G.Map_id)
    have "c \<in> GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using that b
      apply (subst (asm) *)
       apply (simp_all add: G.Vrs_Sb)
      apply (auto simp: swap_def)
      done
    with b have "|UNIV - {a}| \<le>o |GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)|"
      by (intro card_of_mono1) auto
    then have "|UNIV::'a1 set| \<le>o |GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)|"
      by (meson infinite_UNIV infinite_card_of_diff_singl ordIso_ordLeq_trans ordIso_symmetric)
    then have False
      using G.Vrs_bd(1) large' not_ordLeq_ordLess
        ordLeq_ordLess_trans by blast
  }
  then show "b = a"
    by blast
next
  fix b :: 'a2 assume "b \<in> GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" for c :: 'a2
    by (subst eta_natural[of id "b \<leftrightarrow> c" id id a, symmetric, simplified])
      (auto simp: G.Vrs_Sb  G.Map_id image_iff intro!: bexI[of _ b])
  then have "GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Vrs_bd(2) large' exists_fresh exists_univ_eq ordLess_ordLeq_trans)
qed (rule eta_mem)

lemma GVrs_eta'[simp]:
  "GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {a}"
  "GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b assume b: "b \<in> GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  { assume "a \<noteq> b"
    then have *: "\<eta>' a = Gsub (b \<leftrightarrow> c) id (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using eta'_natural[of "b \<leftrightarrow> c" id id id a, symmetric, simplified] that
      by (auto simp: G.Map_id)
    have "c \<in> GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using that b
      apply (subst (asm) *)
       apply (simp_all add: G.Vrs_Sb)
      apply (auto simp: swap_def)
      done
    with b have "|UNIV - {a}| \<le>o |GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)|"
      by (intro card_of_mono1) auto
    then have "|UNIV::'a1 set| \<le>o |GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)|"
      by (meson infinite_UNIV infinite_card_of_diff_singl ordIso_ordLeq_trans ordIso_symmetric)
    then have False
      using G.Vrs_bd(1) large' not_ordLeq_ordLess
        ordLeq_ordLess_trans by blast
  }
  then show "b = a"
    by blast
next
  fix b :: 'a2 assume "b \<in> GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" for c :: 'a2
    by (subst eta'_natural[of id "b \<leftrightarrow> c" id id a, symmetric, simplified])
      (auto simp: G.Vrs_Sb  G.Map_id image_iff intro!: bexI[of _ b])
  then have "GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Vrs_bd(2) large' exists_fresh exists_univ_eq ordLess_ordLeq_trans)
qed (rule eta'_mem)

lemma GSupp_eta[simp]:
  "GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
  "GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b :: 'x1 assume "b \<in> GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, Gbd_type, 'x2) G)" for c :: Gbd_type
    by (subst eta_natural[of id id "\<lambda>x. if x = b then c else (undefined :: Gbd_type)" id a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, Gbd_type, 'x2) G) = UNIV"
    by blast
  moreover have "|UNIV :: Gbd_type set| =o Gbd"
    using card_of_unique G.infinite_regular_card_order
      infinite_regular_card_order.card_order ordIso_symmetric by blast
  ultimately show "b \<in> {}"
    by (metis G.Supp_bd(1) not_ordLess_ordIso)
next
  fix b :: 'x2 assume "b \<in> GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, Gbd_type) G)" for c :: Gbd_type
    by (subst eta_natural[of id id id "\<lambda>x. if x = b then c else (undefined :: Gbd_type)" a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, Gbd_type) G) = UNIV"
    by blast
  moreover have "|UNIV :: Gbd_type set| =o Gbd"
    using card_of_unique G.infinite_regular_card_order
      infinite_regular_card_order.card_order ordIso_symmetric by blast
  ultimately show "b \<in> {}"
    by (metis G.Supp_bd(2) not_ordLess_ordIso)
qed

lemma GSupp_eta'[simp]:
  "GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
  "GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b :: 'x1 assume "b \<in> GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, Gbd_type, 'x2) G)" for c :: Gbd_type
    by (subst eta'_natural[of id id "\<lambda>x. if x = b then c else (undefined :: Gbd_type)" id a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, Gbd_type, 'x2) G) = UNIV"
    by blast
  moreover have "|UNIV :: Gbd_type set| =o Gbd"
    using card_of_unique G.infinite_regular_card_order
      infinite_regular_card_order.card_order ordIso_symmetric by blast
  ultimately show "b \<in> {}"
    by (metis G.Supp_bd(1) not_ordLess_ordIso)
next
  fix b :: 'x2 assume "b \<in> GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, Gbd_type) G)" for c :: Gbd_type
    by (subst eta'_natural[of id id id "\<lambda>x. if x = b then c else (undefined :: Gbd_type)" a, symmetric, simplified])
      (auto simp: G.Supp_Sb G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, Gbd_type) G) = UNIV"
    by blast
  moreover have "|UNIV :: Gbd_type set| =o Gbd"
    using card_of_unique G.infinite_regular_card_order
      infinite_regular_card_order.card_order ordIso_symmetric by blast
  ultimately show "b \<in> {}"
    by (metis G.Supp_bd(2) not_ordLess_ordIso)
qed

declare [[typedef_overloaded]]
binder_datatype (EVrs: 'a) E = Ector "('a, x::'a, t::'a E, 'a E) G" binds x in t
  for permute: Eperm
declare E.inject[simp del]

(*for technical reasons we now work with var_E_pre but the classes are the same*)
sublocale var_E_pre < var
  by (rule var_axioms)
sublocale var < var_E_pre
  by standard

lemma
  Eperm_comp:
  "\<And>\<sigma> \<tau>. bij (\<sigma> :: 'a :: var_E_pre \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var_E_pre \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   Eperm \<sigma> o Eperm \<tau> = Eperm (\<sigma> o \<tau>)"
  and EVrs_Eperm:
  "\<And>\<sigma> u. bij (\<sigma> :: 'a :: var_E_pre \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> 
   EVrs (Eperm \<sigma> u) \<subseteq> \<sigma> ` EVrs u"
  and Eperm_cong_id:
  "\<And>\<sigma> e. bij (\<sigma> :: 'a :: var_E_pre \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma> a = a) \<Longrightarrow> Eperm \<sigma> e = e"
  and Eperm_Ector:
  "\<And>\<sigma> u. bij (\<sigma> :: 'a :: var_E_pre \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
    Eperm \<sigma> (Ector u) = Ector (Gren \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u))"
  and Ector_inject: "\<And>x y. (Ector x = Ector y) =
   (\<exists>\<sigma> :: 'a :: var_E_pre \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  and Ector_fresh_surj: "\<And>A e. |A::'a set| <o |UNIV :: 'a::var_E_pre set| \<Longrightarrow> 
    \<exists>u. GVrs2 u \<inter> A = {} \<and> e = Ector u"
  and EVrs_Ector:
  "\<And>u. EVrs (Ector u::('a::var_E_pre) E) =
     GVrs1 u \<union> ((\<Union>e \<in> GSupp1 u. EVrs e) - GVrs2 u) \<union> (\<Union>e \<in> GSupp2 u. EVrs e)"
  and EVrs_bd:
  "\<And>x. |EVrs (x :: 'a :: var_E_pre E)| <o Gbd"
          apply (auto simp: E.inject E.permute_id0 E.permute_comp E.FVars_permute GMAP_def Gren_def E.FVars_bd
             intro: E.permute_cong_id)
  subgoal for A e
    apply (binder_induction e avoiding: A rule: E.strong_induct)
     apply assumption
    apply (rule exI conjI)+
     apply assumption
    apply (rule refl)
    done
  done

inductive subshape where
  "e \<in> GSupp1 u \<union> GSupp2 u \<Longrightarrow> subshape e (Ector u)"

lemma wfp_subshape: "wfp (subshape)"
  apply (rule wfpUNIVI)
  subgoal premises prems for P e
    apply (subgoal_tac "\<And>\<sigma> :: 'a \<Rightarrow> 'a. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> P (Eperm \<sigma> e)")
     apply (drule meta_spec[of _ id])
     apply (simp add: E.permute_id)
    apply (induct e)
    subgoal for u \<sigma>
      apply (rule prems[rule_format])
      apply (auto elim!: subshape.cases simp: G.set_map E.permute_comp  E.inject supp_comp_bound)
      done
    done
  done

lemma subshape_induct: "(\<And>e. (\<And>e'. subshape e' e \<Longrightarrow> P e') \<Longrightarrow> P e) \<Longrightarrow> P e"
  using wfp_subshape
  by (metis wfp_induct)

lemma E_coinduct:
  fixes P and g :: "'k \<Rightarrow> 'a::var_E_pre E" and h e
  assumes "(\<And>k. P k \<Longrightarrow> g k = h k \<or>
    (\<exists>u. g k = Ector (GMAP id id g g u) \<and> h k = Ector (GMAP id id h h u) \<and>
    (\<forall>k \<in> GSupp1 u. P k) \<and> (\<forall>k \<in> GSupp2 u. P k)))"
  shows "P k \<Longrightarrow> g k = h k"
  apply (subgoal_tac "\<And>e. g k = e \<Longrightarrow> e = h k")
   apply blast
  subgoal for e
    apply (induct e arbitrary: k rule: subshape_induct)
    apply (drule assms)
    apply (erule disjE)
     apply simp
    apply (erule exE conjE)+
    apply (auto simp: G.map_comp G.set_map E.permute_id0  E.inject intro!: exI[of _ id] G.map_cong)
     apply (drule meta_spec2, drule meta_mp)
      apply (rule subshape.intros)
      apply (auto simp: E.permute_id0 G.set_map) []
     apply (drule meta_mp)
      apply (erule bspec)
      apply assumption
     apply simp
    apply (drule meta_spec2, drule meta_mp)
     apply (rule subshape.intros)
     apply (auto simp: E.permute_id0 G.set_map) []
    apply (drule meta_mp)
     apply (erule (1) bspec)
    apply simp
    done
  done

context
  fixes \<delta> :: "'a \<Rightarrow> 'a :: var_E_pre" and \<rho> \<rho>' :: "'a ::var_E_pre \<Rightarrow> 'a E"
  assumes small_support:
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var_E_pre)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
begin

lemma permute_\<rho>:
  "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> = {} \<Longrightarrow> Eperm f (\<rho> a) = \<rho> (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho> a = Ector (\<eta> a)")
    apply (simp add: GMAP_def Gren_def eta_natural)
   apply simp
   apply (rule E.permute_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
    apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho> a = Ector (\<eta> a)")
   apply (simp add: GMAP_def Gren_def eta_natural)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done

lemma permute_\<rho>':
  "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>' = {} \<Longrightarrow> Eperm f (\<rho>' a) = \<rho>' (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho>' a = Ector (\<eta>' a)")
    apply (simp add: GMAP_def Gren_def eta'_natural)
   apply simp
   apply (rule E.permute_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
    apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho>' a = Ector (\<eta>' a)")
   apply (simp add: GMAP_def Gren_def eta'_natural)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done

interpretation Esub: QREC_fixed_E "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>'"
  "\<lambda>u. if \<exists>a. Rep_E_pre u = \<eta> a then \<rho> (SOME a. Rep_E_pre u = \<eta> a) else
       if \<exists>a. Rep_E_pre u = \<eta>' a then \<rho>' (SOME a. Rep_E_pre u = \<eta>' a) else
       Ector (GMAP \<delta> id snd snd (Rep_E_pre u))"
  apply standard
    apply (auto intro!: Un_bound simp: E.FVars_bd_UNIVs imsupp_supp_bound small_support) []
   apply (auto simp: map_E_pre_def set2_E_pre_def set3_E_pre_def set4_E_pre_def
     permute_\<rho> permute_\<rho>'
     Abs_E_pre_inverse GMAP_def Gren_def eta_natural eta'_natural small_support imsupp_commute[of _ \<delta>]
     G.Map_Sb[THEN fun_cong, simplified]
     G.Sb_comp[THEN fun_cong, simplified]
     G.Map_comp[THEN fun_cong, simplified] G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb
     Int_Un_distrib eta_distinct eta_distinct' eta_inject eta'_inject Ector_def[symmetric]
     dest: eta_inversion[rotated -1] eta'_inversion[rotated -1])
        apply (force simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def image_iff)
       apply (force simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def image_iff)
      apply (metis Un_iff image_eqI imsupp_def not_in_supp_alt)
     apply (metis Un_iff image_eqI imsupp_def not_in_supp_alt)
    apply (smt (verit, best) Un_iff fst_conv in_mono)
   apply (smt (verit, best) Un_iff fst_conv in_mono)
  apply (smt (verit, best) Un_iff fst_conv in_mono)
  done

definition "Esub = Esub.REC_E"

lemma
  Esub_Ector\<eta>: "Esub (Ector (\<eta> a)) = \<rho> a"
  and Esub_Ector\<eta>': "Esub (Ector (\<eta>' a)) = \<rho>' a"
  and Esub_Ector:
  "GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
   GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  Esub (Ector u) = Ector (Gsub \<delta> id (Gmap Esub Esub u))"
    apply -
  unfolding Esub_def
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set2_E_pre_def Abs_E_pre_inverse noclash_E_def
        eta_distinct GMAP_def Gren_def eta_natural eta_inject)
    done
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set2_E_pre_def Abs_E_pre_inverse noclash_E_def
        eta_distinct' GMAP_def Gren_def eta'_natural eta'_inject)
    done
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set1_E_pre_def set2_E_pre_def set3_E_pre_def set4_E_pre_def
        GMAP_def Gren_def eta_distinct Abs_E_pre_inverse noclash_E_def small_support comp_def[of snd]
        G.Map_Sb[THEN fun_cong, simplified]
        G.Sb_comp[THEN fun_cong, simplified]
        G.Map_comp[THEN fun_cong, simplified]
        dest: eta_inversion[rotated -1] eta'_inversion[rotated -1])
    done
  done

lemma EVrs_Esub: "EVrs (Esub e)
    \<subseteq> EVrs e \<union> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>')"
  unfolding Esub_def
  by (rule Esub.REC_FVars)

lemma Eperm_Esub: "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
  imsupp f \<inter> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>') = {} \<Longrightarrow>
  Eperm f (Esub t) = Esub (Eperm f t)"
  unfolding Esub_def
  by (rule Esub.REC_swap)

end

lemma Eperm_id: "Eperm id = id"
  apply (rule ext)
  apply (rule trans[OF Eperm_cong_id id_apply[symmetric]])
    apply simp_all
  done

lemma Eperm_cong: "bij (\<sigma> :: 'a :: var_E_pre \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
         bij (\<tau> :: 'a :: var_E_pre \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma> a = \<tau> a) \<Longrightarrow> Eperm \<sigma> e = Eperm \<tau> e"
  apply (rule trans[OF _ Eperm_cong_id, of _ "\<sigma> o inv \<tau>"])
     apply (auto simp: Eperm_comp[THEN fun_cong, simplified] supp_comp_bound
       dest: EVrs_Eperm[THEN set_mp, rotated -1] simp flip: o_assoc)
  done

lemma Ector_eta_inj: "Ector u = Ector (\<eta> a) \<longleftrightarrow> u = \<eta> a"
  by (metis Ector_inject eta_natural supp_id_bound Gren_def)

lemma Ector_eta'_inj: "Ector u = Ector (\<eta>' a) \<longleftrightarrow> u = \<eta>' a"
  unfolding Ector_inject
  apply safe
  subgoal for \<sigma>
    apply (drule arg_cong[where f = "Gsub id (inv \<sigma>) o Gmap (Eperm (inv \<sigma>)) id"])
    apply (auto simp: eta'_natural G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
        G.Map_id G.Sb_Inj Eperm_comp Eperm_id Gren_def)
    done
  subgoal
    apply (auto simp: eta'_natural Gren_def)
    done
  done

lemma Ector_eta_inj': "Ector (\<eta> a) = Ector x \<longleftrightarrow> x = \<eta> a"
  using Ector_eta_inj by metis

lemma Ector_eta'_inj': "Ector (\<eta>' a) = Ector x \<longleftrightarrow> x = \<eta>' a"
  using Ector_eta'_inj by metis

lemma EVrs_bound[simp]: "|EVrs (x :: 'a :: var_E_pre E)| <o |UNIV :: 'a set|"
  by (rule ordLess_ordLeq_trans[OF EVrs_bd large'])

lemma GVrs2_bound[simp]: "|GVrs2 (u::('a :: var_E_pre, 'a, 'a E, 'a E) G)| <o |UNIV :: 'a set|"
  by (rule ordLess_ordLeq_trans[OF G.Vrs_bd(2) large'])

lemma Ector_fresh_inject:
  assumes "GVrs2 x \<inter> A = {}" "GVrs2 y \<inter> A = {}" "|A :: 'a::var_E_pre set| <o |UNIV :: 'a set|"
  shows "(Ector x = Ector y) = (\<exists>\<sigma>. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and> imsupp \<sigma> \<inter> A = {}
    \<and> id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  unfolding Ector_inject
  apply (rule iffI; elim exE conjE)
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

lemma Esub_inversion0:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var_E_pre)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>) (\<rho>::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>') (\<rho>'::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
   GVrs2 u \<inter> (imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e \<union> EVrs (Ector u)) = {} \<Longrightarrow>
   \<forall>a. e \<noteq> Ector (\<eta> a) \<Longrightarrow> \<forall>a. e \<noteq> Ector (\<eta>' a) \<Longrightarrow>
   \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a. u \<noteq> \<eta>' a \<Longrightarrow>
   Ector u = Esub \<delta> \<rho> \<rho>' e \<Longrightarrow> \<exists>u'. u = Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u') \<and> GVrs2 u' = GVrs2 u \<and> e = Ector u'"
  apply (insert Ector_fresh_surj[where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e \<union> EVrs (Ector u)" and e = e])
  apply (drule meta_mp)
   apply (auto intro!: Un_bound simp: imsupp_supp_bound) []
  apply (erule exE conjE)+
  apply (simp add: Int_Un_distrib Ector_eta_inj Ector_eta'_inj)
  apply (subst (asm) (2) Esub_Ector; (simp add: Int_Un_distrib Ector_eta_inj Ector_eta'_inj)?)
  apply (drule sym)
  subgoal for u'
    apply (subst (asm) Ector_fresh_inject[where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> (\<Union> (EVrs ` GSupp1 u') - GVrs2 u')"])
       apply (simp_all add: Int_Un_distrib G.Vrs_Sb G.Vrs_Map EVrs_Ector) [2]
      apply (auto intro!: Un_bound UN_bound card_of_minus_bound simp: imsupp_supp_bound ordLess_ordLeq_trans[OF G.Supp_bd(1) large']) []
    apply (erule exE conjE)+
    subgoal for \<sigma>
      apply (rule exI[where x = "Gren id \<sigma> (Gmap (Eperm \<sigma>) id u')"])
      apply (rule conjI)
       apply (erule trans[OF sym])
       apply (auto 0 0 simp add: Int_Un_distrib G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified] Eperm_Esub Ector_inject
          G.Vrs_Sb G.Vrs_Map Gren_def intro!: trans[OF G.Sb_cong arg_cong[where f = "Gsub _ _", OF G.Map_cong]] exI[of _ \<sigma>])
      apply (meson disjoint_iff_not_equal id_on_def not_in_imsupp_same)
      done
    done
  done

lemma Esub_inversion:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var_E_pre)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>) (\<rho>::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>') (\<rho>'::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
   GVrs2 u \<inter> (imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e) = {} \<Longrightarrow>
   \<forall>a. e \<noteq> Ector (\<eta> a) \<Longrightarrow> \<forall>a. e \<noteq> Ector (\<eta>' a) \<Longrightarrow>
   \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a. u \<noteq> \<eta>' a \<Longrightarrow>
   Ector u = Esub \<delta> \<rho> \<rho>' e \<Longrightarrow> \<exists>u'. u = Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u') \<and> GVrs2 u' = GVrs2 u \<and> e = Ector u'"
  by (rule Esub_inversion0) (auto dest!: set_mp[OF EVrs_Esub, rotated -1])

inductive Efreee where 
  GVrs1: "a \<in> GVrs1 u \<Longrightarrow> \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow> Efreee a (Ector u)"
| GSupp1: "e \<in> GSupp1 u \<Longrightarrow> Efreee a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efreee a (Ector u)"
| GSupp2: "e \<in> GSupp2 u \<Longrightarrow> Efreee a e \<Longrightarrow> Efreee a (Ector u)"

binder_inductive (no_auto_equiv) Efreee
  where GVrs1 binds "GVrs2 u"
  | GSupp1 binds "GVrs2 u"
  | GSupp2 binds "GVrs2 u"
  for perms: _ Eperm | supps: _ and EVrs
           apply (auto simp: Eperm_id Eperm_comp[THEN fun_cong, simplified] EVrs_Eperm Eperm_cong[where \<tau>=id] G.Vrs_bd) [8]
  subgoal for R B \<sigma> a e
    apply (elim disj_forward exE conjE; hypsubst_thin)
    subgoal for _ u
      apply (rule exI[of _ "\<sigma> a"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map image_iff Eperm_Ector GMAP_def Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject GMAP_def Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject GMAP_def Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    done
  subgoal premises prems for R B a e
    apply (insert extend_fresh[where A = "{a} \<union> EVrs e" and B = B])
    apply (drule meta_mp) subgoal using prems(3) by auto
    apply (drule meta_mp) subgoal by (intro Un_bound; simp)
    apply (drule meta_mp) subgoal by simp
    apply (elim exE conjE)
    subgoal for \<sigma>
      apply (rule exI[of _ "\<sigma> ` B"])
      apply (rule conjI)
       apply simp
      apply (insert prems(3))
      apply (elim disj_forward exE conjE; hypsubst_thin)
      subgoal for _ u
        apply (rule exI[of _ a])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map Ector_inject EVrs_Ector Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
        done
      subgoal for e u _
        apply (rule exI[of _ "Eperm \<sigma> e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector id_onD[of _ \<sigma> a] Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2] prems(2)[of \<sigma> a e, rotated 2])
        done
      subgoal for e u _
        apply (rule exI[of _ "e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
        done
      done
    done
  done

inductive Efree\<eta> where 
  eta: "Efree\<eta> a (Ector (\<eta> a))"
| GSupp1: "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree\<eta> a (Ector u)"
| GSupp2: "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> Efree\<eta> a (Ector u)"

binder_inductive (no_auto_equiv) Efree\<eta>
  where GSupp1 binds "GVrs2 u"
  | GSupp2 binds "GVrs2 u"
  for perms: _ Eperm | supps: _ and EVrs
          apply (auto simp: Eperm_id Eperm_comp[THEN fun_cong, simplified] EVrs_Eperm Eperm_cong[where \<tau>=id] G.Vrs_bd Eperm_Ector eta_natural) [7]
  subgoal for R B \<sigma> a e
    apply (elim disj_forward exE conjE; hypsubst_thin)
    subgoal for _
      apply (auto simp: Eperm_Ector eta_natural GMAP_def Gren_def)
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject GMAP_def Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject GMAP_def Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    done
  subgoal premises prems for R B a e
    apply (insert extend_fresh[where A = "{a} \<union> EVrs e" and B = B])
    apply (drule meta_mp) subgoal using prems(3) by auto
    apply (drule meta_mp) subgoal by (intro Un_bound; simp)
    apply (drule meta_mp) subgoal by simp
    apply (elim exE conjE)
    subgoal for \<sigma>
      apply (rule exI[of _ "\<sigma> ` B"])
      apply (rule conjI)
       apply simp
      apply (insert prems(3))
      apply (elim disj_forward exE conjE; hypsubst_thin)
      subgoal for _
        apply auto
        done
      subgoal for e u _
        apply (rule exI[of _ "Eperm \<sigma> e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector id_onD[of _ \<sigma> a] Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2] prems(2)[of \<sigma> a e, rotated 2])
        done
      subgoal for e u _
        apply (rule exI[of _ "e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
        done
      done
    done
  done

inductive Efree\<eta>' where 
  eta': "Efree\<eta>' a (Ector (\<eta>' a))"
| GSupp1: "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree\<eta>' a (Ector u)"
| GSupp2: "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> Efree\<eta>' a (Ector u)"

binder_inductive (no_auto_equiv) Efree\<eta>'
  where GSupp1 binds "GVrs2 u"
  | GSupp2 binds "GVrs2 u"
  for perms: _ Eperm | supps: _ and EVrs
          apply (auto simp: Eperm_id Eperm_comp[THEN fun_cong, simplified] EVrs_Eperm Eperm_cong[where \<tau>=id] G.Vrs_bd Eperm_Ector eta_natural) [7]
  subgoal for R B \<sigma> a e
    apply (elim disj_forward exE conjE; hypsubst_thin)
    subgoal for _
      apply (auto simp: Eperm_Ector eta'_natural GMAP_def Gren_def)
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject GMAP_def Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject GMAP_def Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    done
  subgoal premises prems for R B a e
    apply (insert extend_fresh[where A = "{a} \<union> EVrs e" and B = B])
    apply (drule meta_mp) subgoal using prems(3) by auto
    apply (drule meta_mp) subgoal by (intro Un_bound; simp)
    apply (drule meta_mp) subgoal by simp
    apply (elim exE conjE)
    subgoal for \<sigma>
      apply (rule exI[of _ "\<sigma> ` B"])
      apply (rule conjI)
       apply simp
      apply (insert prems(3))
      apply (elim disj_forward exE conjE; hypsubst_thin)
      subgoal for _
        apply auto
        done
      subgoal for e u _
        apply (rule exI[of _ "Eperm \<sigma> e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector id_onD[of _ \<sigma> a] Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2] prems(2)[of \<sigma> a e, rotated 2])
        done
      subgoal for e u _
        apply (rule exI[of _ "e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
        done
      done
    done
  done

definition "EFVrs e = {a. Efreee a e}"
definition "EFVrs\<eta> e = {a. Efree\<eta> a e}"
definition "EFVrs\<eta>' e = {a. Efree\<eta>' a e}"

lemma Esub_unique_fresh:
  assumes
    "|A| <o |UNIV::'a set|"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var_E_pre)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "\<And>a. h (Ector (\<eta> a)) = \<rho> a"
    "\<And>a. h (Ector (\<eta>' a)) = \<rho>' a"
    "\<And>u.
  GVrs2 u \<inter> A = {} \<Longrightarrow>
  GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
  GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  h (Ector u) = Ector (Gsub \<delta> id (Gmap h h u))"
  shows
    "h = Esub \<delta> \<rho> \<rho>'"
  apply (rule ext)
  subgoal for e
    apply (rule E_coinduct[where g=h and h="Esub \<delta> \<rho> \<rho>'" and P="\<lambda>_. True"])
     apply simp_all
    subgoal for e
      apply (insert Ector_fresh_surj[where e = "e" and A = "
         imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>' \<union> EVrs e \<union> A"])
      apply (drule meta_mp)
       apply (auto intro!: Un_bound IImsupp_bound simp: imsupp_supp_bound assms) []
      apply (simp add: Int_Un_distrib)
      apply (erule exE conjE)+
      subgoal for u
        apply (cases "\<exists>a. u = \<eta> a")
         apply (auto simp: Esub_Ector\<eta> assms) []
        apply (cases "\<exists>a. u = \<eta>' a")
         apply (auto simp: Esub_Ector\<eta>' assms) []
        apply (rule disjI2)
        apply (rule exI[where x="Gsub \<delta> id u"])
        apply (auto simp: assms GMAP_def Gren_def G.Sb_Inj Esub_Ector G.Map_Sb[THEN fun_cong, simplified])
        done
      done
    done
  done

lemma SSupp_comp_Esub_le:
  assumes "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "SSupp (Ector \<circ> \<eta>) (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'') \<subseteq>
   SSupp (Ector \<circ> \<eta>) \<rho>'' \<union> SSupp (Ector \<circ> \<eta>) \<rho>"
    "SSupp (Ector \<circ> \<eta>') (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'') \<subseteq>
   SSupp (Ector \<circ> \<eta>') \<rho>'' \<union> SSupp (Ector \<circ> \<eta>') \<rho>'"
  using assms
  by (auto simp: SSupp_def Esub_Ector\<eta> Esub_Ector\<eta>')

lemma SSupp_comp_bound[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>''| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'')| <o |UNIV :: 'a set|"
  apply (rule ordLeq_ordLess_trans)
   apply (erule (2) card_of_mono1[OF SSupp_comp_Esub_le(1)])
  apply (auto simp: Un_bound)
  done

lemma SSupp_comp_bound'[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>''| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'')| <o |UNIV :: 'a set|"
  apply (rule ordLeq_ordLess_trans)
   apply (erule (2) card_of_mono1[OF SSupp_comp_Esub_le(2)])
  apply (auto simp: Un_bound)
  done

lemma EFVrs\<eta>_Ector_eta: "EFVrs\<eta> (Ector (\<eta> a)) = {a}"
  unfolding EFVrs\<eta>_def
  apply (auto intro: Efree\<eta>.intros)
  subgoal for x
    apply (induct "Ector (\<eta> a)" pred: Efree\<eta>)
      apply (auto simp: Ector_eta_inj dest: eta_inj)
    done
  done

lemma EFVrs\<eta>'_Ector_eta': "EFVrs\<eta>' (Ector (\<eta>' a)) = {a}"
  unfolding EFVrs\<eta>'_def
  apply (auto intro: Efree\<eta>'.intros)
  subgoal for x
    apply (induct "Ector (\<eta>' a)" pred: Efree\<eta>')
      apply (auto simp: Ector_eta'_inj dest: eta'_inj)
    done
  done

lemma Efree_alt:
  "Efreee a e \<longleftrightarrow> a \<in> EFVrs e"
  "Efree\<eta> a e \<longleftrightarrow> a \<in> EFVrs\<eta> e"
  "Efree\<eta>' a e \<longleftrightarrow> a \<in> EFVrs\<eta>' e"
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def by auto

lemma Efreee_Efree: "Efreee a e \<Longrightarrow> a \<in> EVrs e"
  by (induct e pred: Efreee) (auto simp: EVrs_Ector)
lemma Efree\<eta>_Efree: "Efree\<eta> a e \<Longrightarrow> a \<in> EVrs e"
  by (induct e pred: Efree\<eta>) (auto simp: EVrs_Ector)
lemma Efree\<eta>'_Efree: "Efree\<eta>' a e \<Longrightarrow> a \<in> EVrs e"
  by (induct e pred: Efree\<eta>') (auto simp: EVrs_Ector)

lemma EFVrs_bd:
  "|EFVrs (x :: 'a :: var_E_pre E)| <o Gbd"
  "|EFVrs\<eta> (x :: 'a :: var_E_pre E)| <o Gbd"
  "|EFVrs\<eta>' (x :: 'a :: var_E_pre E)| <o Gbd"
    apply (meson EVrs_bd Efree_alt(1) Efreee_Efree card_of_subset_bound subset_eq)
   apply (meson EVrs_bd Efree_alt(2) Efree\<eta>_Efree card_of_subset_bound subset_eq)
  apply (meson EVrs_bd Efree_alt(3) Efree\<eta>'_Efree card_of_subset_bound subset_eq)
  done

lemma EFVrs_bound[simp]:
  "|EFVrs (x :: 'a :: var_E_pre E)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta> (x :: 'a :: var_E_pre E)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta>' (x :: 'a :: var_E_pre E)| <o |UNIV :: 'a set|"
  using EFVrs_bd large' ordLess_ordLeq_trans by blast+

lemma EFVrs_EsubI1[OF _ _ _ _ refl]:
  assumes
    "z \<in> EFVrs e"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
     "e' = e"
  shows "\<delta> z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,5) unfolding EFVrs_def mem_Collect_eq
  apply (binder_induction z e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efreee.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  apply hypsubst_thin
  subgoal for a u
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
    apply (rule Efreee.intros)
      apply (simp add: G.Vrs_Sb G.Vrs_Map assms(2-4))
    subgoal by (meson eta_inversion assms(2) supp_id_bound)
    subgoal by (meson eta'_inversion assms(2) supp_id_bound)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
      apply fastforce
     apply fastforce
    apply (rule Efreee.intros(2))
      apply (simp add: G.Supp_Sb G.Supp_Map assms(2-4))
      apply (erule imageI)
     apply assumption
    apply (simp add: G.Vrs_Sb G.Vrs_Map assms(2-4))
    apply (metis imsupp_empty_IntD1)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
      apply fastforce
     apply fastforce
    apply (rule Efreee.intros(3))
     apply (simp add: G.Supp_Sb G.Supp_Map assms(2-4))
     apply (erule imageI)
    apply assumption
    done
  done

lemma EFVrs_EsubI2[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs_def EFVrs\<eta>_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efreee.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (metis Ector_eta_inj Efreee.cases GSupp_eta(1,2) empty_iff)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EVrs \<rho>")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efreee_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efreee.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs_EsubI3[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs_def EFVrs\<eta>'_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>'.strong_induct)
       apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>'; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efreee.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (metis Ector_eta'_inj Efreee.cases GSupp_eta'(1,2) empty_iff)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>'_def Efreee_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efreee.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs_EsubD:
  assumes
    "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> \<delta> ` EFVrs e \<union>
  ((\<Union>x\<in>EFVrs\<eta> e. EFVrs (\<rho> x)) \<union>
   (\<Union>x\<in>EFVrs\<eta>' e. EFVrs (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (binder_induction z "Esub \<delta> \<rho> \<rho>' e" arbitrary: e avoiding:
      "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e"
      rule: Efreee.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a u e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(1) Efreee.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1) Efreee.intros(1))
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply blast
       apply blast
      apply blast
     apply blast
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Vrs_Sb)
    unfolding G.Vrs_Map
    using Efreee.intros(1) by fastforce
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efreee.intros(2) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efreee.intros(2) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
        apply (smt (verit, del_insts) Efreee.intros(2)
          Un_empty image_iff imsupp_empty_IntD1 mem_Collect_eq)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (cases "\<rho> a = Ector (\<eta> a)")
         apply (metis Ector_eta_inj Efreee.cases GSupp_eta(1,2) empty_iff)
        apply (smt (verit, ccfv_threshold) Efree\<eta>.intros(2) IImsupp'_def SSupp_def Un_iff comp_apply
            disjoint_iff_not_equal mem_Collect_eq)
        done
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (cases "\<rho>' a = Ector (\<eta>' a)")
         apply (metis Ector_eta'_inj Efreee.cases GSupp_eta'(1,2) empty_iff)
        apply (smt (verit, ccfv_threshold) Efree\<eta>'.intros(2) IImsupp'_def SSupp_def Un_iff comp_apply
            disjoint_iff_not_equal mem_Collect_eq)
        done
      done
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efreee.intros(3) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efreee.intros(3) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    apply (elim disj_forward ex_forward; assumption?)
      apply (smt (verit, del_insts) Efreee.intros(3)
        Un_empty image_iff imsupp_empty_IntD1 mem_Collect_eq)
     apply (metis Efree\<eta>.intros(3))
    apply (metis Efree\<eta>'.intros(3))
    done
  done

lemma EFVrs\<eta>_EsubI2[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs\<eta> (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs\<eta>_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (simp add: EFVrs\<eta>_Ector_eta Efree_alt(2))
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EVrs \<rho>")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efree\<eta>_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs\<eta>_EsubI3[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs\<eta> (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>'.strong_induct)
       apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>'; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (metis Ector_eta'_inj Efree\<eta>.cases GSupp_eta'(1,2) empty_iff eta_distinct)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>'_def Efree\<eta>_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs\<eta>_EsubD:
  assumes
    "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> ((\<Union>x\<in>EFVrs\<eta> e. EFVrs\<eta> (\<rho> x)) \<union> (\<Union>x\<in>EFVrs\<eta>' e. EFVrs\<eta> (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (binder_induction z "Esub \<delta> \<rho> \<rho>' e" arbitrary: e avoiding:
      "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e"
      rule: Efree\<eta>.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1) Efree\<eta>.intros(1))
    apply (insert Ector_fresh_surj[of "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e" e, simplified])
    apply (drule meta_mp)
     apply (auto simp: assms imsupp_supp_bound Un_bound) []
    apply (auto simp: Ector_eta_inj Ector_eta'_inj Esub_Ector Int_Un_distrib assms(2-4))
    apply (metis Ector_eta_inj assms(2) eta_inversion supp_id_bound)
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(2) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>.intros(2) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
       apply (metis (mono_tags, lifting) EFVrs\<eta>_Ector_eta Efree\<eta>.GSupp1 Efree_alt(2) IImsupp'_def
          Int_emptyD SSupp_def Un_iff comp_apply mem_Collect_eq singletonD)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (smt (verit, ccfv_threshold) Ector_eta'_inj' Efree\<eta>'.GSupp1 Efree\<eta>.simps
            GSupp_eta'(1,2) IImsupp'_def SSupp_def Un_iff all_not_in_conv comp_apply disjoint_iff
            eta_distinct mem_Collect_eq)
        done
      done
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(3) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>.intros(3) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    apply (elim disj_forward ex_forward; assumption?)
     apply (metis Efree\<eta>.intros(3))
    apply (metis Efree\<eta>'.intros(3))
    done
  done

lemma EFVrs\<eta>'_EsubI2[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs\<eta>' (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>.strong_induct)
       apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (metis Ector_eta_inj Efree\<eta>'.cases GSupp_eta(1,2) empty_iff eta_distinct)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EVrs \<rho>")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>'_def Efree\<eta>'_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs\<eta>'_EsubI3[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs\<eta>' (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs\<eta>'_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>'.strong_induct)
       apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>'; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (simp add: EFVrs\<eta>'_Ector_eta' Efree_alt(3))
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>'_def Efree\<eta>'_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs\<eta>'_EsubD:
  assumes
    "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var_E_pre)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> ((\<Union>x\<in>EFVrs\<eta> e. EFVrs\<eta>' (\<rho> x)) \<union> (\<Union>x\<in>EFVrs\<eta>' e. EFVrs\<eta>' (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (binder_induction z "Esub \<delta> \<rho> \<rho>' e" arbitrary: e avoiding:
      "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e"
      rule: Efree\<eta>'.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(1) Efree\<eta>'.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1))
    apply (insert Ector_fresh_surj[of "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e" e, simplified])
    apply (drule meta_mp)
     apply (auto simp: assms imsupp_supp_bound Un_bound) []
    apply (auto simp: Ector_eta_inj Ector_eta'_inj Esub_Ector Int_Un_distrib assms(2-4))
    apply (metis Ector_eta'_inj assms(2) eta'_inversion supp_id_bound)
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>'.intros(2) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(2) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
       apply (smt (verit, ccfv_threshold) Ector_eta_inj Efree\<eta>'.simps Efree\<eta>.intros(2)
          GSupp_eta(1,2) GVrs_eta'(1) GVrs_eta(1) IImsupp'_def SSupp_def Un_iff comp_apply
          disjoint_iff disjoint_single empty_iff mem_Collect_eq)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (metis (mono_tags, lifting) EFVrs\<eta>'_Ector_eta' Efree\<eta>'.GSupp1 Efree_alt(3) IImsupp'_def
            Int_Un_distrib Int_emptyD SSupp_def Un_empty comp_apply mem_Collect_eq singletonD)
        done
      done
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>'.intros(3) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(3) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    apply (elim disj_forward ex_forward; assumption?)
     apply (metis Efree\<eta>.intros(3))
    apply (metis Efree\<eta>'.intros(3))
    done
  done

(*
declare [[goals_limit=18]]
pbmv_monad "'a::var_E_pre E"
  Sbs: Esub
  RVrs: EFVrs
  Injs: "Ector o \<eta>" "Ector o \<eta>'"
  Vrs: EFVrs\<eta> EFVrs\<eta>'
  bd: Gbd
  oops
*)

lemma E_pbmv_axioms:
 "infinite_regular_card_order Gbd"
 "Esub id (Ector \<circ> \<eta>) (Ector \<circ> \<eta>') = id"
 "\<And>f \<rho>1 \<rho>2.
       |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
       Esub f \<rho>1 \<rho>2 \<circ> (Ector \<circ> \<eta>) = \<rho>1"
 "\<And>f \<rho>1 \<rho>2.
       |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
       Esub f \<rho>1 \<rho>2 \<circ> (Ector \<circ> \<eta>') = \<rho>2"
 "\<And>g \<rho>'1 \<rho>'2 f \<rho>1 \<rho>2.
       |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
       |supp g| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>'1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>'2| <o |UNIV :: 'a set| \<Longrightarrow>
       Esub g \<rho>'1 \<rho>'2 \<circ> Esub f \<rho>1 \<rho>2 =
       Esub (g \<circ> f) (Esub g \<rho>'1 \<rho>'2 \<circ> \<rho>1) (Esub g \<rho>'1 \<rho>'2 \<circ> \<rho>2)"
 "\<And>x. |EFVrs x| <o Gbd"
 "\<And>x. |EFVrs\<eta> x| <o Gbd"
 "\<And>x. |EFVrs\<eta>' x| <o Gbd"
 "\<And>a. EFVrs ((Ector \<circ> \<eta>) a) = {}"
 "\<And>a. EFVrs ((Ector \<circ> \<eta>') a) = {}"
 "\<And>a. EFVrs\<eta> ((Ector \<circ> \<eta>) a) = {a}"
 "\<And>a. EFVrs\<eta> ((Ector \<circ> \<eta>') a) = {}"
 "\<And>a. EFVrs\<eta>' ((Ector \<circ> \<eta>) a) = {}"
 "\<And>a. EFVrs\<eta>' ((Ector \<circ> \<eta>') a) = {a}"
 "\<And>f \<rho>1 \<rho>2 x.
        |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs (Esub f \<rho>1 \<rho>2 x) =
        f ` EFVrs x \<union>
        ((\<Union>x\<in>EFVrs\<eta> x. EFVrs (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs (\<rho>2 x)))"
 "\<And>f \<rho>1 \<rho>2 x.
        |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs\<eta> (Esub f \<rho>1 \<rho>2 x) =
        (\<Union>x\<in>EFVrs\<eta> x. EFVrs\<eta> (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs\<eta> (\<rho>2 x))"
 "\<And>f \<rho>1 \<rho>2 x.
        |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs\<eta>' (Esub f \<rho>1 \<rho>2 x) =
        (\<Union>x\<in>EFVrs\<eta> x. EFVrs\<eta>' (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs\<eta>' (\<rho>2 x))"
 "\<And>f \<rho>1 \<rho>2 g \<rho>'1 \<rho>'2 x.
        |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        |supp g| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>'1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>'2| <o |UNIV :: 'a set| \<Longrightarrow>
        (\<And>a. a \<in> EFVrs x \<Longrightarrow> f a = g a) \<Longrightarrow>
        (\<And>a. a \<in> EFVrs\<eta> x \<Longrightarrow> \<rho>1 a = \<rho>'1 a) \<Longrightarrow>
        (\<And>a. a \<in> EFVrs\<eta>' x \<Longrightarrow> \<rho>2 a = \<rho>'2 a) \<Longrightarrow>
        Esub f \<rho>1 \<rho>2 x = Esub g \<rho>'1 \<rho>'2 x"
  subgoal
    by (rule G.infinite_regular_card_order)
  subgoal
    apply (rule Esub_unique_fresh[symmetric, where A="{}"])
          apply (simp_all add: G.Sb_Inj G.Map_id)
    done
  subgoal for \<delta> \<rho> \<rho>'
    by (simp add: fun_eq_iff Esub_Ector\<eta>)
  subgoal
    by (simp add: fun_eq_iff Esub_Ector\<eta>')
  subgoal for \<delta>1 \<rho>1 \<rho>1' \<delta>2 \<rho>2 \<rho>2'
    apply (rule Esub_unique_fresh[where A = "imsupp \<delta>1 \<union> imsupp \<delta>2 \<union>
   IImsupp' (Ector o \<eta>) EVrs \<rho>1 \<union> IImsupp' (Ector o \<eta>) EVrs \<rho>2 \<union>
   IImsupp' (Ector o \<eta>') EVrs \<rho>1' \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>2'"])
          apply (simp_all add: supp_comp_bound Esub_Ector\<eta> Esub_Ector\<eta>' Esub_Ector Un_bound
        imsupp_supp_bound Int_Un_distrib)
    apply (subst Esub_Ector;
        (simp add: EVrs_Ector G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Int_Un_distrib G.Map_comp[THEN fun_cong, simplified]
          G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified])?)
      apply (rule conjI)
    apply (metis Int_commute Int_image_imsupp)
    subgoal for u
      apply safe
      apply (drule set_mp[OF EVrs_Esub, rotated -1]; simp?)
      apply fast
      done
    subgoal by (meson eta_inversion supp_id_bound)
    subgoal by (meson eta'_inversion supp_id_bound)
    done
  subgoal by (rule EFVrs_bd)
  subgoal by (rule EFVrs_bd)
  subgoal by (rule EFVrs_bd)
  subgoal for x
    by (auto simp: EFVrs_def Ector_eta_inj' elim: Efreee.cases)
  subgoal for x
    by (auto simp: EFVrs_def Ector_eta'_inj' elim: Efreee.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>_def Ector_eta_inj' eta_inj elim: Efree\<eta>.cases intro: Efree\<eta>.intros)
  subgoal for x
    by (auto simp: EFVrs\<eta>_def Ector_eta'_inj' eta_distinct elim: Efree\<eta>.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>'_def Ector_eta_inj' dest!: eta_distinct[THEN notE, OF sym] elim: Efree\<eta>'.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>'_def Ector_eta'_inj' eta'_inj elim: Efree\<eta>'.cases intro: Efree\<eta>'.intros)
  subgoal for \<delta> \<rho> \<rho>' x
    by (auto intro: EFVrs_EsubI1 EFVrs_EsubI2 EFVrs_EsubI3 dest: EFVrs_EsubD)
  subgoal for \<delta> \<rho> \<rho>' x
    by (auto intro: EFVrs\<eta>_EsubI2 EFVrs\<eta>_EsubI3 dest: EFVrs\<eta>_EsubD)
  subgoal for \<delta> \<rho> \<rho>' x 
    by (auto intro: EFVrs\<eta>'_EsubI2 EFVrs\<eta>'_EsubI3 dest: EFVrs\<eta>'_EsubD)
  subgoal for \<delta>1 \<rho>1 \<rho>1' \<delta>2 \<rho>2 \<rho>2' e
    apply (rule E_coinduct[where g="Esub \<delta>1 \<rho>1 \<rho>1'" and h="Esub \<delta>2 \<rho>2 \<rho>2'" and k = e
          and P = "\<lambda>e. (\<forall>a \<in> EFVrs e. \<delta>1 a = \<delta>2 a) \<and> (\<forall>a \<in> EFVrs\<eta> e. \<rho>1 a = \<rho>2 a) \<and> (\<forall>a \<in> EFVrs\<eta>' e. \<rho>1' a = \<rho>2' a)", rotated -1])
     apply blast
    subgoal premises prems for e
      thm prems
      apply (insert prems(1-6,10-))
      apply (cases "\<exists>a. e = Ector (\<eta> a)")
       apply (auto simp: Esub_Ector\<eta> EFVrs\<eta>_Ector_eta) []
      apply (cases "\<exists>a. e = Ector (\<eta>' a)")
       apply (auto simp: Esub_Ector\<eta>' EFVrs\<eta>'_Ector_eta') []
      apply (rule disjI2)
      apply (insert Ector_fresh_surj[where e = "e" and A = "
         imsupp \<delta>1 \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>1 \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>1' \<union>
         imsupp \<delta>2 \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>2 \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>2' \<union> EVrs e"])
      apply (drule meta_mp)
       apply (auto intro!: Un_bound IImsupp_bound simp: imsupp_supp_bound) []
      apply (simp add: Int_Un_distrib)
      apply (erule exE conjE)+
      apply hypsubst_thin
      subgoal for u
        apply (rule exI[where x="Gsub \<delta>2 id u"])
        apply (simp add: G.Supp_Sb Esub_Ector Ector_eta_inj Ector_eta'_inj
            G.Map_Sb[THEN fun_cong, simplified] GMAP_def Gren_def G.Sb_Inj)
        apply (intro conjI ballI)
              apply (rule arg_cong[where f = Ector])
              apply (rule G.Sb_cong; (simp add: G.Vrs_Map)?)
              apply (metis EFVrs_def GVrs1 mem_Collect_eq)
             apply (metis Efree_alt(1) Efreee.GSupp1
            imsupp_empty_IntD2)
        subgoal for e a
          apply (cases "a \<in> GVrs2 u")
           apply (metis (mono_tags) IImsupp'_def Int_emptyD SSupp_def Un_iff mem_Collect_eq)
          apply (meson Efree\<eta>.GSupp1 Efree_alt(2))
          done
        subgoal for e a
          apply (cases "a \<in> GVrs2 u")
           apply (metis (mono_tags) IImsupp'_def Int_emptyD SSupp_def Un_iff mem_Collect_eq)
          apply (meson Efree\<eta>'.GSupp1 Efree_alt(3))
          done
          apply (meson Efree_alt(1) Efreee.GSupp2)
         apply (meson Efree\<eta>.simps Efree_alt(2))
        apply (meson Efree\<eta>'.simps Efree_alt(3))
        done
      done
    done
  done
unused_thms

end