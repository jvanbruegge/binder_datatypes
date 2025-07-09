theory Unique_Fixpoint_Codata
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

consts Grel :: "('x1 \<Rightarrow> 'x1' \<Rightarrow> bool) \<Rightarrow> ('x2 \<Rightarrow> 'x2' \<Rightarrow> bool) \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G \<Rightarrow> ('a1, 'a2, 'x1', 'x2') G \<Rightarrow> bool"

setup \<open>Sign.mandatory_path "G"\<close>

axiomatization where
  rel_compp: "\<And>R1 R2 S1 S2. Grel R1 R2 OO Grel S1 S2 \<le> Grel (R1 OO S1) (R2 OO S2)" and
  in_rel: "\<And>f1 f2 R1 R2 x y.
       |supp (f1 :: 'a1 \<Rightarrow> 'a1 :: var)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       bij f2 \<Longrightarrow>
       |supp (f2 :: 'a2 \<Rightarrow> 'a2 :: var)| <o |UNIV :: 'a2 set| \<Longrightarrow>
       Grel R1 R2 (GMAP f1 f2 id id x) y =
       (\<exists>z. (GSupp1 z \<subseteq> {(x, y). R1 x y} \<and> GSupp2 z \<subseteq> {(x, y). R2 x y}) \<and>
            GMAP id id fst fst z = x \<and> GMAP f1 f2 snd snd z = y)" and
  wit1: "GSupp1 Gwit = {}" and
  wit2: "GSupp2 Gwit = {}"
lemmas wit = G.wit1 G.wit2
setup \<open>Sign.parent_path\<close>

definition "Gpred \<equiv> \<lambda>P1 P2 x. Ball (GSupp1 x) P1 \<and> Ball (GSupp2 x) P2"

declare [[typedef_overloaded]]
mrbnf "('a1::var, 'a2::var, 'x1, 'x2) G"
  map: GMAP
  sets: free: GVrs1 bound: GVrs2 live: GSupp1 live: GSupp2
  bd: Gbd
  wits: Gwit
  rel: Grel
  pred: Gpred
  var_class: var
                 apply (auto simp: GMAP_def Gren_def G.Sb_Inj G.Map_id fun_eq_iff G.infinite_regular_card_order G.wit
     G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
     G.Vrs_Sb G.Supp_Sb G.Vrs_Map G.Supp_Map G.Vrs_bd G.Supp_bd
     intro: trans[OF G.Sb_cong arg_cong[where f="Gsub _ _", OF G.Map_cong]]) [12]
     apply (rule G.rel_compp)
    apply (rule G.in_rel; assumption)
    apply (simp_all add: G.wit Gpred_def)
  done
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

(*codatatype declaration (no high-level syntax implemented yet); morally corresponds to
binder_codatatype (EVrs: 'a) E = Ector "('a, x::'a, t::'a E, 'a E) G" binds x in t
  for permute: Eperm
*)
local_setup \<open>fn lthy =>
let
  val (fp_res, lthy) = MRBNF_FP.construct_binder_fp BNF_Util.Greatest_FP
    [{
      FVars = [SOME "EVrs"],
      T_name = "E",
      nrecs = 2,
      permute = SOME "Eperm",
      pre_mrbnf = the (MRBNF_Def.mrbnf_of lthy @{type_name G})
    }]
    [[([], [0])]]
    lthy
  val raw_fps = fp_res |> #raw_fps |> hd |> @{print}
in lthy end
\<close>
ML \<open>val E_raw_fps = MRBNF_FP_Def_Sugar.fp_result_of @{context} @{type_name E} |> the |> #raw_fps |> hd\<close>

abbreviation "Ector \<equiv> E_ctor"

(*for technical reasons we now work with covar_G instead of covar but the classes are the same*)
sublocale covar_G < covar
  by standard (simp_all add: large regular)
sublocale covar < covar_G
  by standard (simp_all add: large regular)

typedef wit_covar_G = "UNIV :: Gbd_type suc set"
  by blast
instantiation wit_covar_G :: covar_G begin
instance
proof
  have *: "|UNIV :: wit_covar_G set| =o card_suc Gbd"
    by (metis bij_imp_bij_inv card_of_card_order_on card_of_unique2 card_order_card_suc
      card_suc_alt ordIso_symmetric type_definition_bij_betw_Abs
      type_definition_wit_covar_G)
  from * show "cardSuc Gbd \<le>o |UNIV :: wit_covar_G set|"
    by (meson G.bd_card_order cardSuc_ordIso_card_suc ordIso_iff_ordLeq ordIso_ordLeq_trans)
  from * show "regularCard |UNIV :: wit_covar_G set|"
    using Cinfinite_card_suc G.bd_Cinfinite G.bd_card_order ordIso_symmetric regularCard_card_suc
      regularCard_ordIso by blast
qed
end

lemma
  Eperm_comp:
  "\<And>\<sigma> \<tau>. bij (\<sigma> :: 'a :: covar_G \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: covar_G \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   Eperm \<sigma> o Eperm \<tau> = Eperm (\<sigma> o \<tau>)"
  and EVrs_Eperm:
  "\<And>\<sigma> u. bij (\<sigma> :: 'a :: covar_G \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> 
   EVrs (Eperm \<sigma> u) \<subseteq> \<sigma> ` EVrs u"
  and Eperm_cong_id:
  "\<And>\<sigma> e. bij (\<sigma> :: 'a :: covar_G \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma> a = a) \<Longrightarrow> Eperm \<sigma> e = e"
  and Eperm_Ector:
  "\<And>\<sigma> u. bij (\<sigma> :: 'a :: covar_G \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
    Eperm \<sigma> (Ector u) = Ector (Gren \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u))"
  and Ector_inject: "\<And>x y. (Ector x = Ector y) =
   (\<exists>\<sigma> :: 'a :: covar_G \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  and Ector_fresh_surj: "\<And>A e. |A::'a set| <o |UNIV :: 'a::covar_G set| \<Longrightarrow> 
    \<exists>u. GVrs2 u \<inter> A = {} \<and> e = Ector u"
  and EVrs_Ector:
  "\<And>u. EVrs (Ector u::('a::covar_G) E) =
     GVrs1 u \<union> ((\<Union>e \<in> GSupp1 u. EVrs e) - GVrs2 u) \<union> (\<Union>e \<in> GSupp2 u. EVrs e)"
  and EVrs_bd:
  "\<And>x. |EVrs (x :: 'a :: covar_G E)| <o card_suc Gbd"
          apply (auto simp: E.TT_inject0 E.permute_id0 E.permute_comp E.FVars_permute GMAP_def Gren_def E.FVars_bd
            E.permute_ctor E.FVars_ctor intro: E.permute_cong_id)
  apply (meson E.TT_fresh_cases)
  done

lemma E_coinduct:
  fixes P and g :: "'k \<Rightarrow> 'a::covar_G E" and h e
  assumes "(\<And>k. P k \<Longrightarrow> g k = h k \<or>
    (\<exists>u. g k = Ector (GMAP id id g g u) \<and> h k = Ector (GMAP id id h h u) \<and>
    (\<forall>k \<in> GSupp1 u. P k) \<and> (\<forall>k \<in> GSupp2 u. P k)))"
  shows "P k \<Longrightarrow> g k = h k"
  apply (coinduction arbitrary: k rule: E.existential_coinduct)
  apply (drule sym)
  apply (drule sym)
  apply (drule assms)
  apply (erule disjE)
   apply (metis (mono_tags, lifting) G.rel_refl)
  apply (erule exE conjE)+
  subgoal for x y k u
    apply (rule exI[where x = "GMAP id id g g u"])
    apply (rule exI[where x = "GMAP id id h h u"])
    apply (intro conjI)
    apply simp
     apply simp
    apply (auto simp: G.rel_map intro!: G.rel_refl_strong)
    done
  done

lemma Eperm_id: "Eperm id = id"
  apply (rule ext)
  apply (rule trans[OF Eperm_cong_id id_apply[symmetric]])
    apply simp_all
  done

lemma Eperm_cong: "bij (\<sigma> :: 'a :: covar_G \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
         bij (\<tau> :: 'a :: covar_G \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
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

lemma rel_set_reflI: "(\<And>a. a \<in> A \<Longrightarrow> r a a) \<Longrightarrow> rel_set r A A"
  by (auto simp: rel_set_def)

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV::'a set| then f else id"

abbreviation "E_abs \<equiv> quot_type.abs alpha_E Abs_E"
abbreviation "E_rep \<equiv> quot_type.rep Rep_E"

lemma alpha_refls: "alpha_E x x"
  by (tactic \<open>resolve_tac @{context} [E_raw_fps |> #inner |> #alpha_refl] 1\<close>)
lemma alpha_syms: "alpha_E x y \<Longrightarrow> alpha_E y x"
  by (tactic \<open>resolve_tac @{context} [E_raw_fps |> #inner |> #alpha_sym] 1\<close>)
lemma alpha_trans: "alpha_E x y \<Longrightarrow> alpha_E y z \<Longrightarrow> alpha_E x z"
  by (tactic \<open>resolve_tac @{context} [E_raw_fps |> #inner |> #alpha_trans] 1\<close>)
lemma alpha_FVars: "alpha_E x y \<Longrightarrow> EVrs_raw x = EVrs_raw y"
  by (tactic \<open>resolve_tac @{context} (E_raw_fps |> #inner |> #alpha_FVarss) 1\<close>)
lemma alpha_bij_eqs:
  fixes f::"'a::covar_G \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
  shows "alpha_E (Eperm_raw f x) (Eperm_raw f y) = alpha_E x y"
  by (tactic \<open>resolve_tac @{context} [E_raw_fps |> #inner |> #alpha_bij_eq] 1\<close>) (rule assms)+

lemma EVrs_raw_Eperm_raw:
  fixes f::"'a::covar_G \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
  shows "EVrs_raw (Eperm_raw f x) = f ` EVrs_raw x"
  by (tactic \<open>resolve_tac @{context} (E_raw_fps |> #FVars_permutes) 1\<close>) (rule assms)+
lemma Eperm_raw_id:
  shows "Eperm_raw id x = x"
  by (tactic \<open>resolve_tac @{context} [E_raw_fps |> #permute_id] 1\<close>)
lemma Eperm_raw_comp:
  fixes f g::"'a::covar_G \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "Eperm_raw f (Eperm_raw g x) = Eperm_raw (f o g) x"
  by (tactic \<open>resolve_tac @{context} [E_raw_fps |> #permute_comp] 1\<close>) (rule assms)+

lemma E_Quotients: "Quotient alpha_E E_abs E_rep (\<lambda>x. (=) (E_abs x))"
  apply (subgoal_tac "Quotient3 alpha_E E_abs E_rep")
   prefer 2
   apply (rule quot_type.Quotient)
   apply (rule type_definition_quot_type)
    apply (rule type_definition_E)
   apply (rule equivpI)
     apply (rule reflpI)
     apply (rule alpha_refls)
    apply (rule sympI)
    apply (erule alpha_syms)
   apply (rule transpI)
   apply (erule alpha_trans)
   apply assumption
  apply (rule QuotientI)
     apply (erule Quotient3_abs_rep)
    apply (rule alpha_refls)
   apply (erule Quotient3_rel[symmetric])
  apply (rule ext)+
  apply (rule iffI)
   apply (rule conjI)
    apply (rule alpha_refls)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemmas E_total_abs_eq_iffs = E_Quotients[THEN Quotient_total_abs_eq_iff, OF reflpI[OF alpha_refls]]
lemmas E_rep_abs = E_Quotients[THEN Quotient_rep_abs, OF alpha_refls]
lemmas E_abs_rep = E_Quotients[THEN Quotient_abs_rep]

lemmas E_rep_abs_syms = alpha_syms[OF E_rep_abs]

lemma E_abs_ctors: "E_abs (raw_E_ctor x) = Ector (GMAP id id E_abs E_abs x)"
  by (rule E.abs_ctor)

lemma Eperm_E_abs:
  fixes f::"'a::covar_G \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "Eperm f (E_abs x) = E_abs (Eperm_raw f x)"
  apply (unfold Eperm_def)
  apply (rule E_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_bij_eqs[THEN iffD2, OF assms])
  apply (rule E_rep_abs)
  done

(* Definitions *)

locale COREC =
  fixes Udtor :: "'u \<Rightarrow> ('a::covar_G, 'a, 'a E + 'u, 'a E + 'u) G set"
  and Umap :: "('a::covar_G \<Rightarrow> 'a) \<Rightarrow> 'u \<Rightarrow> 'u"
  and UFVars :: "'u \<Rightarrow> 'a::covar_G set"
  and valid_U :: "'u \<Rightarrow> bool"
  assumes Udtor_ne: "\<And>d. valid_U d \<Longrightarrow> Udtor d \<noteq> {}"
    and alpha_Udtor: "\<And>X X' d. valid_U d \<Longrightarrow> {X,X'} \<subseteq> Udtor d \<Longrightarrow>
\<exists>u. bij (u::'a::covar_G \<Rightarrow> 'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on ((\<Union>z \<in> GSupp1 X. case_sum EVrs UFVars z) - GVrs2 X) u \<and>
     GMAP id u (map_sum (Eperm u) (Umap u)) id X = X'"
    and
    (* The dual of the first block of assumptions from Norrish's paper:   *)
    UFVars_Udtor:
    "\<And> d X. valid_U d \<Longrightarrow> X \<in> Udtor d \<Longrightarrow>
  GVrs1 X \<union> (\<Union>z \<in> GSupp2 X. case_sum EVrs UFVars z) \<union>
   ((\<Union>z \<in> GSupp1 X. case_sum EVrs UFVars z) - GVrs2 X) \<subseteq>
  UFVars d"
    and
    (* The dual of the third block: *)
    Umap_Udtor: "\<And>u d. valid_U d \<Longrightarrow>
  bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::'a::covar_G set| \<Longrightarrow>
  Udtor (Umap u d) \<subseteq>
  image
    (GMAP u u (map_sum (Eperm u) (Umap u)) (map_sum (Eperm u) (Umap u)))
    (Udtor d)"
    and Umap_comp: "valid_U d \<Longrightarrow> bij f \<Longrightarrow> |supp (f::'a::covar_G \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij g \<Longrightarrow> |supp (g::'a::covar_G \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> Umap f (Umap g d) = Umap (f \<circ> g) d"
    and Umap_cong0: "valid_U d \<Longrightarrow> bij f \<Longrightarrow> |supp (f::'a::covar_G \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> (\<And>a. a \<in> UFVars d \<Longrightarrow> f a = a) \<Longrightarrow> Umap f d = d"
    and valid_Umap: "bij f \<Longrightarrow> |supp (f::'a::covar_G \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> valid_U d \<Longrightarrow> valid_U (Umap f d)"
    and valid_Udtor: "\<And>x. valid_U d \<Longrightarrow> x \<in> Udtor d \<Longrightarrow> Gpred (pred_sum (\<lambda>_. True) valid_U)  (pred_sum (\<lambda>_. True) valid_U) x"
begin

lemma Umap_id: "valid_U d \<Longrightarrow> Umap id d = d"
  apply (rule Umap_cong0)
  apply assumption
    apply (rule bij_id supp_id_bound)+
  apply (rule id_apply)
  done

lemma valid_Udtor': "\<And>x z r. valid_U d \<Longrightarrow> x \<in> Udtor d \<Longrightarrow> z \<in> GSupp1 x \<union> GSupp2 x \<Longrightarrow> r \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U r"
  apply (drule valid_Udtor)
   apply assumption
  apply (erule UnE)
  (* REPEAT_DETERM *)
   apply (unfold G.pred_set)
   apply (erule conjE)
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (unfold sum.pred_set)
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* repeated *)
   apply (erule conjE)
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
  apply assumption
  done

lemma Umap_Udtor_strong:
  assumes u: "bij (u::'a::covar_G\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and "valid_U d"
  shows
    "Udtor (Umap u d) =
 image
   (GMAP u u (map_sum (Eperm u) (Umap u)) (map_sum (Eperm u) (Umap u)))
   (Udtor d)"
proof -
  have x: "d = Umap (inv u) (Umap u d)"
    apply (rule sym)
    apply (rule trans[OF Umap_comp])
         apply (rule bij_imp_bij_inv supp_inv_bound assms)+
    apply (subst inv_o_simp1, rule assms)+
    apply (rule trans[OF Umap_id])
     apply (rule assms)
    apply (rule refl)
    done
  show ?thesis
    apply (rule subset_antisym)
     apply (rule Umap_Udtor[OF assms(3,1,2)])
    apply (subst x)
    apply (rule image_subsetI)
    apply (drule Umap_Udtor[THEN subsetD, rotated -1])
       apply (rule bij_imp_bij_inv supp_inv_bound assms valid_Umap)+
    apply (erule imageE)
    apply hypsubst
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]])
     apply (rule G.map_comp)
          apply (rule bij_imp_bij_inv supp_inv_bound assms)+
    apply (unfold map_sum.comp)
    apply (subst inv_o_simp2 E.permute_comp0 Umap_comp, (rule bij_imp_bij_inv supp_inv_bound assms)+)+
    apply (unfold comp_def)
    apply (unfold Umap_id E.permute_id0 map_sum.id G.map_id)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule G.map_cong[rotated -5])
               apply (rule refl)
              apply (rule refl)
             apply (rule refl)
      (* REPEAT_DETERM *)
            apply (rule sum.map_cong0[OF refl])
            apply (drule valid_Udtor'[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule arg_cong2[OF _ refl, of _ _ Umap])
             apply (rule inv_o_simp2)
             apply (rule assms)
            apply (rule Umap_id)
            apply assumption
      (* repeated *)
           apply (rule sum.map_cong0[OF refl])
           apply (drule valid_Udtor'[rotated])
              apply (erule UnI2 UnI1)
             apply assumption
            apply (rule valid_Umap)
              apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
           apply (rule trans)
            apply (rule Umap_comp)
                apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
           apply (rule trans)
            apply (rule arg_cong2[OF _ refl, of _ _ Umap])
            apply (rule inv_o_simp2)
            apply (rule assms)
           apply (rule Umap_id)
           apply assumption
      (* END REPEAT_DETERM *)
          apply (rule supp_id_bound bij_id)+
    apply (unfold Umap_id E.permute_id0 map_sum.id G.map_id id_def[symmetric])
    apply assumption
    done
qed

definition FFVarsBD :: "('a::covar_G, 'a, 'a E + 'u, 'a E + 'u) G \<Rightarrow> 'a set" where
  "FFVarsBD X \<equiv> (\<Union>z \<in> GSupp1 X. case_sum EVrs UFVars z) - GVrs2 X"

lemmas Udtor_Umap = alpha_Udtor[folded FFVarsBD_def]
lemmas EVrs_Udtor = UFVars_Udtor[folded FFVarsBD_def]

(*************************************)
(* The raw-E-based model infrastructure *)
term Rep_E
find_consts "_ \<Rightarrow> _ raw_E"

definition Utor :: "'u \<Rightarrow> ('a::covar_G, 'a, 'a raw_E + 'u, 'a raw_E + 'u) G set" where
  "Utor d \<equiv>  GMAP id id (map_sum E_rep id) (map_sum E_rep id) ` (Udtor d)"

abbreviation raw_Umap :: "('a::covar_G \<Rightarrow> 'a) \<Rightarrow> 'u \<Rightarrow> 'u" where
  "raw_Umap \<equiv> Umap"

abbreviation raw_UFVars :: "'u \<Rightarrow> 'a::covar_G set" where
  "raw_UFVars \<equiv> UFVars"

definition raw_UFVarsBD :: "('a::covar_G, 'a, 'a raw_E + 'u, 'a raw_E + 'u) G \<Rightarrow> 'a set" where
  "raw_UFVarsBD X \<equiv> \<Union>(case_sum EVrs_raw raw_UFVars ` GSupp1 X) - GVrs2 X"

lemmas raw_UFVars_def2 = trans[OF meta_eq_to_obj_eq[OF EVrs_def[of "E_abs _"]] alpha_FVars[OF E_rep_abs], symmetric]

(* PreE-based version of the assumptions: *)

(*  *)
lemmas raw_Umap_id = Umap_id

lemmas raw_Umap_comp = Umap_comp

lemma FVarsBD_FFVarsBD:
  "raw_UFVarsBD X = FFVarsBD (GMAP id id (map_sum E_abs id) (map_sum E_abs id) X)"
  apply (unfold raw_UFVarsBD_def FFVarsBD_def raw_UFVars_def2)
  apply (subst G.set_map[OF supp_id_bound bij_id supp_id_bound])+
  apply (subst image_id)
  apply (subst image_image)
  apply (subst case_sum_map_sum)
  apply (subst comp_id)
  apply (subst comp_def)
  apply (rule refl)
  done

lemmas supp_comp_bound = supp_comp_bound[OF _ _ infinite_UNIV]

lemma abs_rep_id: "E_abs o E_rep = id"
  apply (unfold comp_def)
  apply (subst E_abs_rep)
  apply (fold id_def)
  apply (rule refl)
  done

lemma DTOR_mapD:
  assumes "valid_U d"
  shows "{X,X'} \<subseteq> Utor d \<Longrightarrow> \<exists>u. bij (u::'a::covar_G\<Rightarrow>'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD X) u \<and>
     mr_rel_G id u
       (rel_sum (\<lambda> t t'. alpha_E (Eperm_raw u t) t') (\<lambda> d d'. raw_Umap u d = d'))
(rel_sum alpha_E (=))
     X X'"
  apply (drule image_mono[of _ _ "GMAP id id (map_sum E_abs id) (map_sum E_abs id)"])
  apply (unfold image_insert image_empty Utor_def image_comp)
  apply (subst (asm) G.map_comp0[symmetric], (rule supp_id_bound bij_id)+)
  apply (unfold id_o map_sum.comp abs_rep_id map_sum.id G.map_id0 image_id)
  apply (drule alpha_Udtor[OF assms])
  apply (erule exE conjE)+
  apply (subst (asm) G.set_map G.map_comp, (rule supp_id_bound bij_id | assumption)+)+
  apply (unfold image_id id_o o_id map_sum.comp)
  apply (drule G.mr_rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
  apply (subst (asm) G.mr_rel_map, (rule supp_id_bound bij_id | assumption)+)
  apply (unfold id_o o_id)
  apply (subst (asm) G.mr_rel_map, (rule supp_id_bound bij_id | assumption)+)
  apply (unfold inv_id id_o o_id relcompp_conversep_Grp)
  apply (unfold Grp_OO)
  apply (rule exI)+
  apply (rule conjI[rotated])+
     apply (erule G.mr_rel_mono_strong0[rotated -5])
              apply (rule ballI, rule refl)+
    (* REPEAT_DETERM *)
            apply (rule ballI impI)+
            apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
            apply (unfold sum.rel_map comp_def id_apply)[1]
            apply (erule sum.rel_mono_strong)
  find_theorems Eperm Eperm_raw
             apply (subst (asm) Eperm_E_abs, assumption+)?
             apply (drule E_total_abs_eq_iffs[THEN iffD1])
             apply assumption
            apply assumption
    (* repeated *)
           apply (rule ballI impI)+
           apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
           apply (unfold sum.rel_map comp_def id_apply)[1]
           apply (erule sum.rel_mono_strong)
            apply (subst (asm) Eperm_E_abs, assumption+)?
            apply (drule E_total_abs_eq_iffs[THEN iffD1])
            apply assumption
           apply assumption
    (* END REPEAT_DETERM *)
          apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold raw_UFVarsBD_def raw_UFVars_def2 image_comp[unfolded comp_def] case_sum_map_sum o_id)
    apply (unfold comp_def)
    apply assumption+
  done

lemma Utor_ne:
  "valid_U d \<Longrightarrow> Utor d \<noteq> {}"
  by (unfold Utor_def arg_cong[OF image_is_empty, of Not])
    (erule Udtor_ne)

lemma Utor_abs_Udtor: "X \<in> Utor d \<Longrightarrow> GMAP id id (map_sum E_abs id) (map_sum E_abs id) X \<in> Udtor d"
  apply (unfold Utor_def)
  apply (erule imageE)
  apply hypsubst_thin
  apply (subst G.map_comp)
    apply (rule supp_id_bound bij_id)+
  apply (subst map_sum.comp)+
  apply (subst id_o)+
  apply (subst abs_rep_id)+
  apply (subst map_sum.id)+
  apply (subst G.map_id)
  apply assumption
  done

lemma raw_UFVars_Utor:
  assumes "valid_U d"
  shows "X \<in> Utor d \<Longrightarrow> GVrs1 X \<union> \<Union>(case_sum EVrs_raw raw_UFVars ` GSupp2 X) \<union> raw_UFVarsBD X \<subseteq> raw_UFVars d"
  apply (drule EVrs_Udtor[OF assms Utor_abs_Udtor])
  apply (subst (asm) G.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_comp case_sum_o_map_sum o_id image_id raw_UFVars_def2)
  apply (unfold FVarsBD_FFVarsBD comp_def)
  apply assumption
  done

lemma raw_Umap_Utor:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar_G set|"
    and valid_d: "valid_U d"
  shows
    "rel_set
  (mr_rel_G u u
     (rel_sum (\<lambda> t t'. alpha_E (Eperm_raw u t) t') (\<lambda> d d'. raw_Umap u d = d'))
     (rel_sum (\<lambda> t t'. alpha_E (Eperm_raw u t) t') (\<lambda> d d'. raw_Umap u d = d')))
 (Utor d)
 (Utor (raw_Umap u d))"
  apply (unfold Utor_def)
  apply (subst Umap_Udtor_strong[OF u, of d])
  apply (rule valid_d)
  apply (subst image_comp)
  apply (subst G.map_comp0[symmetric])
      apply (rule assms supp_id_bound bij_id)+
  apply (subst map_sum.comp)+
  apply (subst id_o)+
  apply (subst rel_set_image)+
  apply (rule rel_set_reflI)
  apply (subst G.mr_rel_map)
      apply (rule supp_id_bound bij_id u)+
  apply (subst o_id)+
  apply (subst G.mr_rel_map | rule u)+
  apply (subst inv_o_simp1 | rule u)+
  apply (unfold relcompp_conversep_Grp Grp_OO G.mr_rel_id[symmetric])
  apply (subst sum.rel_map)+
  apply (unfold Eperm_def)
  apply (rule G.rel_refl)
    (* REPEAT *)
   apply (rule sum.rel_refl)
    apply (subst comp_apply)
    apply (rule E_rep_abs_syms)
   apply (subst id_apply)
   apply (rule refl)
    (* REPEAT *)
  apply (rule sum.rel_refl)
   apply (subst comp_apply)
   apply (rule E_rep_abs_syms)
  apply (subst id_apply)
  apply (rule refl)
  done

definition suitable ::  "('u \<Rightarrow> ('a, 'a, 'a raw_E + 'u,'a raw_E + 'u) G) \<Rightarrow> bool" where
  "suitable pick \<equiv> \<forall> d. valid_U d \<longrightarrow> pick d \<in> Utor d"
definition f :: "('u \<Rightarrow> ('a::covar_G,'a,'a raw_E + 'u,'a raw_E + 'u) G) \<Rightarrow> 'u => 'a raw_E" where
  "f pick \<equiv> corec_raw_E pick"
definition pick0 :: "'u \<Rightarrow> ('a, 'a, 'a raw_E + 'u, 'a raw_E + 'u) G" where
  "pick0 \<equiv> SOME pick. suitable pick"
definition f0 :: "'u \<Rightarrow> 'a raw_E" where
  "f0 \<equiv> f pick0"
definition COREC :: "'u \<Rightarrow> 'a E" where
  "COREC d = E_abs (f0 d)"

lemma f_simps:
  "f pick d = raw_E_ctor (GMAP id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d))"
  apply(subst raw_E.corec[of pick, unfolded f_def[symmetric]])
  apply (unfold id_def)
  apply (rule refl)
  done

lemma f_ctor:
  assumes "raw_E_ctor x = f pick d"
  shows "x = GMAP id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d)"
  by (rule trans[OF assms f_simps, unfolded raw_E.inject])

lemma suitable_FVarsD:
  assumes "suitable pick" "valid_U d"
  shows "GVrs1 (pick d) \<union> \<Union>(case_sum EVrs_raw raw_UFVars ` GSupp2 (pick d)) \<union> raw_UFVarsBD (pick d)
       \<subseteq> raw_UFVars d"
  by (rule raw_UFVars_Utor[OF assms(2) assms(1)[unfolded suitable_def, THEN spec, THEN mp, OF assms(2)]])

lemma f_FVarsD_aux:
  assumes "is_free_raw_E a t"
    "(\<And>d. valid_U d \<Longrightarrow> t = f pick d \<Longrightarrow> a \<in> raw_UFVars d)"
    "pred_sum (\<lambda>_. True) valid_U td"
  shows "t = case_sum id (f pick) td \<Longrightarrow> a \<in> case_sum EVrs_raw raw_UFVars td"
  apply (rule sumE[of td])
   apply hypsubst
   apply (subst sum.case)
   apply (unfold EVrs_raw_def mem_Collect_eq)
   apply (insert assms(1))[1]
   apply (hypsubst_thin)
   apply (subst (asm) sum.case)
   apply (subst (asm) id_apply)
   apply assumption
  apply hypsubst
  apply (subst sum.case)
  apply (rule assms(2))
   apply (unfold sum.simps)
   apply (insert assms(3))[1]
   apply hypsubst_thin
   apply (subst (asm) pred_sum_inject)
  apply assumption
  apply assumption
  done

lemma valid_pick_set3: "suitable pick \<Longrightarrow> xc \<in> GSupp1 (pick xb) \<Longrightarrow> valid_U xb \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U xc"
  apply (unfold suitable_def Utor_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor xb"])
  apply (simp only:)
  apply (subst (asm) G.set_map, (rule supp_id_bound bij_id)+)
  apply (cases xc)
  apply hypsubst_thin
   apply (subst pred_sum.simps)
   apply simp
  apply hypsubst_thin
  apply (subst pred_sum.simps)
  apply (rule disjI2)
  apply (rule exI)
  apply (rule conjI)
   apply (rule refl)
  apply (rule imageE)
  prefer 2
  apply (erule valid_Udtor')
     apply assumption
    prefer 3
  apply assumption
   apply (rule UnI1)
   apply assumption
  apply (subst sum.set_map[of _ id, unfolded image_id, symmetric])
  apply (rule setr.intros)
  apply (rule sym)
  apply assumption
  done

lemma valid_pick_set4: "suitable pick \<Longrightarrow> xc \<in> GSupp2 (pick xb) \<Longrightarrow> valid_U xb \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U xc"
  apply (unfold suitable_def Utor_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor xb"])
  apply (simp only:)
  apply (subst (asm) G.set_map, (rule supp_id_bound bij_id)+)
  apply (cases xc)
  apply hypsubst_thin
   apply (subst pred_sum.simps)
   apply simp
  apply hypsubst_thin
  apply (subst pred_sum.simps)
  apply (rule disjI2)
  apply (rule exI)
  apply (rule conjI)
   apply (rule refl)
  apply (rule imageE)
  prefer 2
  apply (erule valid_Udtor')
     apply assumption
    prefer 3
  apply assumption
   apply (rule UnI2)
   apply assumption
  apply (subst sum.set_map[of _ id, unfolded image_id, symmetric])
  apply (rule setr.intros)
  apply (rule sym)
  apply assumption
  done

lemma f_FVarsD:
  assumes p: "suitable pick"
and valid_d: "valid_U d"
  shows "EVrs_raw (f pick d) \<subseteq> raw_UFVars d"
  apply (rule subsetI)
  apply (unfold EVrs_raw_def mem_Collect_eq)
  apply (erule is_free_raw_E.induct[of _ _ "\<lambda>x y. \<forall>d. valid_U d \<longrightarrow> y = f pick d \<longrightarrow> x \<in> raw_UFVars d", THEN spec, THEN mp, THEN mp[OF _ refl]])
     prefer 4
     apply (rule valid_d)


     apply (rule allI)
    apply (rule impI)+
    apply (rule le_supE[OF suitable_FVarsD[OF assms(1), unfolded Un_assoc]])
  prefer 2
     apply (erule subsetD)
    apply (drule f_ctor)
    apply hypsubst
    apply (subst (asm) G.set_map)
      apply (rule supp_id_bound bij_id)+
    apply (unfold image_id)
     apply assumption

  prefer 2

(* REPEAT_DETERM *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) G.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
  thm f_FVarsD_aux
   apply (drule f_FVarsD_aux)
     apply (erule allE)
      apply (erule impE)
       prefer 2
  apply (erule impE)
      apply assumption
        apply assumption
  apply assumption
     prefer 2
  apply (rule refl)
     prefer 2
   apply (rule suitable_FVarsD[THEN subsetD, unfolded raw_UFVarsBD_def, rotated]) (* TODO: put union members in correct order *)
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 2 2] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
  prefer 2
    apply assumption
   apply (drule valid_pick_set3[OF p])
    apply assumption
  apply assumption
    (* repeated *)
(* TODO: this not actually a repeat anymore, reorganize the proof
to recover that property *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) G.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
   apply (drule f_FVarsD_aux)
     apply (erule allE)
      apply (erule impE)
       prefer 2
  apply (erule impE)
      apply assumption
        apply assumption
  apply assumption
     prefer 2
  apply (rule refl)
     prefer 2
   apply (rule suitable_FVarsD[THEN subsetD, unfolded raw_UFVarsBD_def, rotated]) (* TODO: put union members in correct order *)
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 2 1] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
   apply (rule assms)
  apply (rule valid_pick_set4[OF p])
  prefer 2
   apply assumption
  apply assumption
  done
    (* END REPEAT_DETERM *)
find_theorems Eperm_raw
lemma OO_permute:
  assumes "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar_G set|"
          "bij (v::'a\<Rightarrow>'a)" "|supp v| <o |UNIV::'a::covar_G set|"
  shows "((\<lambda>t. alpha_E (Eperm_raw v t)) OO (\<lambda>t. alpha_E (Eperm_raw u t))) = (\<lambda>t. alpha_E (Eperm_raw (u \<circ> v) t))"
  apply (unfold Eperm_raw_comp[OF assms, symmetric])
  apply (rule ext)
  apply (rule ext)
  apply (rule iffI)
  apply (subst (asm) relcompp.simps)
   apply (erule exE)+
   apply (erule conjE)+
   apply hypsubst
   apply (erule alpha_trans[rotated])
   apply (subst alpha_bij_eqs, (rule assms)+)
   apply assumption
  apply (subst relcompp.simps)
  apply (rule exI)+
  apply (rule conjI[rotated])+
  prefer 2
     apply (rule alpha_refls)
    apply assumption
   apply (rule refl)+
  done


lemma OO_comp:
  assumes "\<And>d. valid_U d \<Longrightarrow> (g u \<circ> g v) d = g (u \<circ> v) d"
  shows "valid_U x \<Longrightarrow> ((\<lambda>d. (=) (g v d)) OO (\<lambda>d. (=) (g u d))) x = (\<lambda>d. (=) (g (u \<circ> v) d)) x"
  apply (subst (2) Grp_UNIV_def[symmetric])
  apply (subst (2) Grp_UNIV_def[symmetric])
  apply (subst Grp_o[symmetric])
  apply (unfold Grp_UNIV_def)
  apply (subst assms)
  apply assumption
  apply (rule refl)
  done

lemma OO_raw_Umap:
  assumes "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar_G set|"
          "bij (v::'a\<Rightarrow>'a)" "|supp v| <o |UNIV::'a::covar_G set|"
        shows "valid_U x \<Longrightarrow> ((\<lambda>d. (=) (raw_Umap v d)) OO (\<lambda>d. (=) (raw_Umap u d))) x  = (\<lambda>d. (=) (raw_Umap (u \<circ> v) d)) x"
  apply (rule OO_comp)
  apply (subst comp_apply)
   apply (rule Umap_comp[OF _ assms])
   apply assumption+
  done

lemma OO_alpha_permute:
  assumes  "bij (g::'a \<Rightarrow> 'a)" "|supp g| <o |UNIV::'a::covar_G set|"
  shows "alpha_E OO (\<lambda>t. alpha_E (Eperm_raw g t)) = (\<lambda>t. alpha_E (Eperm_raw g t))"
  apply (rule ext)
  apply (rule ext)
  apply (rule iffI)
  prefer 2
   apply (rule relcomppI)
    prefer 2
    apply assumption
   apply (rule alpha_refls)
  apply (erule relcomppE)
  apply (subst (asm) alpha_bij_eqs[OF assms, symmetric])
  apply (erule alpha_trans)
  apply assumption
  done


lemma set3_setr_valid:
  assumes "suitable pick"
and "valid_U d"
and "z \<in> GSupp1 (pick d)"
shows "x \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U x"
  by (rule valid_pick_set3[OF assms(1,3,2), THEN sum.pred_set[THEN fun_cong, THEN iffD1, THEN conjunct2], THEN bspec])

lemma rel_F_suitable_mapD:
  assumes valid_d: "valid_U d"
    and pp': "suitable pick" "suitable pick'"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar_G set|"
  shows "\<exists> v. bij v \<and> |supp v| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD (pick d)) v \<and>
 mr_rel_G u (u o v)
   (rel_sum (\<lambda>t t'. alpha_E (Eperm_raw (u o v) t) t')
            (\<lambda>d d'. raw_Umap (u o v) d = d'))
   (rel_sum (\<lambda>t t'. alpha_E (Eperm_raw u t) t')
            (\<lambda>t t'. raw_Umap u t = t'))
 (pick d)
 (pick' (raw_Umap u d))"
  apply (rule raw_Umap_Utor[OF u valid_d, unfolded rel_set_def, THEN conjunct2, THEN bspec, THEN bexE])
   apply (rule allE)
    apply (rule pp'(2)[unfolded suitable_def])
   apply (erule impE)
    prefer 2
    apply assumption
   apply (rule valid_Umap, (rule u valid_d)+)
  apply (rule exE)
   apply (rule DTOR_mapD[OF assms(1)])
   apply (unfold insert_subset)
   apply (rule conjI)
    apply (rule assms(2)[unfolded suitable_def, THEN spec, THEN mp, OF assms(1)])
   apply (rule conjI)
    apply assumption
   apply (rule empty_subsetI)
  apply (erule conjE)+
  apply(rule exI)
  apply (rule conjI[rotated])+
     apply(rule G.mr_rel_mono_strong0[rotated -5])
               apply (rule G.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI])
                      apply assumption+
                    apply (rule supp_id_bound)
                   apply assumption+
                 apply (rule u)+
              apply (subst o_id)
              apply (rule ballI)
              apply (rule refl)
             apply (rule ballI)
             apply (rule refl)
            apply (rule ballI)+
            apply (rule impI)
            apply (unfold sum.rel_compp[symmetric])
            apply (subst OO_permute[OF u, symmetric])
              apply assumption+
            apply (erule sum.rel_cong[OF refl refl, THEN iffD1, rotated -1])
             apply (rule refl)
            apply (subst OO_raw_Umap[OF u])
               apply assumption+
             apply (erule set3_setr_valid[OF pp'(1) valid_d])
             apply assumption
            apply (rule refl)
            apply (rule ballI)+
           apply (rule impI)
           apply (erule sum.rel_cong[OF refl refl, THEN iffD1, rotated -1])
            apply (subst OO_alpha_permute[OF u])
  apply (rule refl)
           apply (subst eq_OO)
           apply (rule iffI)
            apply assumption
           apply assumption
          apply (subst o_id)
          apply (rule u)
         apply (rule bij_comp[OF _ u(1)])
         apply assumption
        apply (rule supp_comp_bound[OF _ u(2)])
        apply assumption
       apply (rule u)
      apply (rule bij_comp[OF _ u(1)])
      apply assumption
     apply (rule supp_comp_bound[OF _ u(2)])
     apply assumption+
  done

abbreviation (input) "FVarsB x \<equiv> \<Union>(EVrs_raw ` GSupp1 x) - GVrs2 x"

lemma alpha_coinduct2[consumes 1, case_names C]: 
  fixes t t' :: "'a::covar_G raw_E"
  assumes 0: "\<phi> t t'" and 1:
    "\<And>x x' :: ('a,'a,'a raw_E,'a raw_E) G. \<phi> (raw_E_ctor x) (raw_E_ctor x') \<Longrightarrow>
    \<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and>
    id_on (FVarsB x) f \<and> 
    mr_rel_G id f 
 (\<lambda>t t'.  \<phi> (Eperm_raw f t) t' \<or> alpha_E (Eperm_raw f t) t')
 (\<lambda>t t'. \<phi> t t' \<or> alpha_E t t')
       x x'"
  shows "alpha_E t t'"
  apply(rule alpha_E.coinduct[of \<phi>, OF 0])  
  subgoal for x1 x2
    apply (rule raw_E.exhaust[of x1])
    apply (rule raw_E.exhaust[of x2])
    apply hypsubst_thin
    apply (drule 1)
    apply (erule exE)
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply assumption
    done
  done

(* The "monster lemma": swapping and "pick"-irrelevance covered in one shot: *)

lemma f_swap_alpha_xL:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar_G set|"
    and x: "raw_E_ctor x = Eperm_raw u (f pick d)"
  shows "x = GMAP u u (Eperm_raw u \<circ> case_sum id (f pick)) (Eperm_raw u \<circ> case_sum id (f pick)) (pick d)"
  apply (insert x)
  apply (subst (asm) f_simps[of "pick"])
  apply (subst (asm) Eperm_raw.ctr)
  apply (subst (asm) raw_E.inject)
  apply (subst (asm) raw_E.sel)
  apply hypsubst_thin
  apply (subst G.map_comp, (rule supp_id_bound bij_id u supp_comp_bound bij_comp)+)+
  apply (unfold o_id id_o)
  apply (rule refl)
  done

lemma l_is_inr:
  assumes
    r: "rel_sum (\<lambda>t. alpha_E (Eperm_raw u t)) (\<lambda>d d'. raw_Umap u d = d') ttdL ttdR"
    and na: "\<not> alpha_E (Eperm_raw u (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
  shows "\<exists>tL. ttdL = Inr tL"
  apply (rule sumE[of ttdR])
   apply (insert r na)
   apply hypsubst_thin
   apply (subst (asm) sum.case)+
   apply (unfold id_apply)
   apply (rule sumE[of ttdL])
    apply hypsubst_thin
    apply (subst (asm) rel_sum_simps)
  apply (subst (asm) sum.case)
   apply (drule cnf.clause2raw_notE)
     apply assumption
  apply (erule FalseE)
   apply hypsubst_thin
   apply (rule exI)
   apply (rule refl)
  apply (rule sumE[of ttdL])
   apply hypsubst_thin
   apply (subst (asm) rel_sum_simps)
   apply (erule FalseE)
  apply hypsubst_thin
  apply (rule exI)
  apply (rule refl)
  done

lemma r_is_Umap:
  assumes
    r: "rel_sum (\<lambda>t. alpha_E (Eperm_raw u t)) (\<lambda>d d'. raw_Umap u d = d') ttdL ttdR"
    and ttdL: "ttdL = Inr x"
  shows "ttdR = Inr (raw_Umap u x)"
  apply (insert r ttdL)
  apply hypsubst_thin
  apply (unfold rel_sum.simps)
  apply (erule disjE)
   apply (erule exE)+
   apply (erule conjE)
   apply (subst (asm) Inr_Inl_False)
   apply (erule FalseE)
  apply (erule exE)+
  apply (erule conjE)+
  apply (subst (asm) sum.inject)
  apply hypsubst_thin
  apply (rule refl)
  done

lemma f_swap_alpha:
  assumes p: "suitable pick" and p': "suitable pick'"
    and valid_d: "valid_U d"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar_G set|"
  shows "alpha_E (Eperm_raw u (f pick d)) (f pick' (raw_Umap u d))"
   apply (rule alpha_coinduct2[of "\<lambda> tL tR. \<exists> u d. valid_U d \<and> bij u \<and> |supp u| <o |UNIV::'a set| \<and>
   tL = Eperm_raw u (f pick d) \<and> tR = f pick' (raw_Umap u d)"])
  prefer 2
  apply (erule exE conjE)+
  apply (frule rel_F_suitable_mapD[OF _ p p'])
    apply assumption+
  apply (erule exE)
  apply (rule exI)+
  apply (rule conjI[rotated])+
     prefer 4
     apply (rule bij_comp)
      apply (rule bij_imp_bij_inv)
      apply assumption
     apply (rule bij_comp)
      prefer 2
      apply assumption
     apply (erule conjE)
     apply (rotate_tac -2)
     apply assumption
    prefer 3
    apply (rule supp_comp_bound)
     apply (rule supp_inv_bound)
      apply assumption
     apply assumption
    apply (rule supp_comp_bound)
     apply (erule conjE)+
     apply assumption
    apply assumption
   prefer 2

   apply (rule id_on_antimono)
    apply (unfold id_on_def)
    apply (rule allI)
    apply (rule impI)
    apply (subst comp_assoc)
    apply (subst comp_apply)
    apply (subst comp_apply)
    apply (frule bij_inv_rev[THEN iffD1, THEN sym])
     prefer 2
     apply assumption
    apply (erule conjE)+
    apply (erule allE)
    apply (erule impE)
     prefer 2
     apply assumption
    apply (rule image_inv_f_f[OF bij_is_inj, THEN arg_cong2[OF refl, of _ _ "(\<in>)"], THEN iffD1])
     prefer 2
     apply (erule imageI)
    apply assumption
   apply (subst f_swap_alpha_xL[of _ _ "pick"])
      apply assumption+
   apply (subst G.set_map, (rule supp_id_bound bij_id | assumption)+)+
   apply (subst Diff_subset_conv)
   apply (subst image_comp)
   apply (subst comp_assoc[symmetric])
    apply (subst comp_def)
   apply (subst EVrs_raw_Eperm_raw, assumption+)
  apply (subst comp_def[of _ EVrs_raw, symmetric])
   apply (subst comp_assoc)
   apply (subst image_comp[symmetric])
   apply (subst f_swap_alpha_xL[of _ _ "pick"])
      apply assumption+
   apply (subst G.set_map, (rule supp_id_bound bij_id | assumption)+)+
   apply (subst image_Un[symmetric])
   apply (subst image_Union[symmetric])
   apply (rule image_mono)
   apply (unfold raw_UFVarsBD_def)
   apply (subst Un_Diff_cancel)
   apply (rule le_supI2)
   apply (subst o_case_sum)
   apply (unfold o_id)
   apply (rule UN_mono)
    apply (rule subset_refl)
  subgoal for _ _ _ _ _ x
    apply (rule sumE[of x])
     apply hypsubst_thin
     apply (unfold sum.simps)
     apply (rule subset_refl)
    apply hypsubst_thin
    apply (unfold sum.simps)
    apply (subst comp_apply)
    apply (rule f_FVarsD[OF p])
    apply (drule valid_pick_set3[OF p])
     apply assumption
    apply (unfold pred_sum_inject)
    apply assumption
    done
  apply (erule conjE)+
  apply (rotate_tac -6)
  apply (drule f_swap_alpha_xL[of _ _ "pick", rotated -1], assumption+)
  apply (drule f_ctor)
  apply hypsubst
  apply (subst G.mr_rel_map, (assumption | rule supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound)+)
  apply (subst G.mr_rel_map, (assumption | rule supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound bij_id)+)
  apply (subst relcompp_conversep_Grp)+
  apply (subst Grp_OO)+
  apply (unfold id_o inv_id)
  apply (subst (2) comp_assoc)
  apply (subst inv_o_simp1, assumption)
  apply (unfold o_id)
  apply (subst comp_apply)+
  apply (subst Eperm_raw_comp, (assumption | rule supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound)+)
  apply (erule G.mr_rel_mono_strong0[rotated -5])
           apply (rule ballI)
           apply (rule refl)
          apply (rule ballI)
          apply (rule refl)
         apply (rule ballI)+
         apply (rule impI)
         apply (subst Eperm_raw_comp)
             prefer 6

              apply (rule ballI)+
              apply (rule impI)
              apply (rotate_tac -1)
              apply (subst disj_commute)
             apply (rule verit_and_neg)
              apply (frule l_is_inr[of _ _ _ pick "pick'"])
               apply assumption
              apply (erule exE)
              apply hypsubst
              apply (subst sum.case)+
              apply (rule exI)+
              apply (drule r_is_Umap)
               apply (rule refl)
              apply hypsubst
              apply (unfold sum.case)
              apply (rule conjI[rotated])+
                  apply (rule refl)+
                apply assumption+
              apply (drule valid_pick_set4[rotated])
                apply assumption
               apply (rule p)
              apply (unfold pred_sum_inject)
              apply assumption

             prefer 5

             apply (subst (2) comp_assoc)
             apply (subst (3) comp_assoc)
             apply (unfold inv_o_simp1)
              apply (unfold o_id)
              apply (rotate_tac -1)
              apply (subst disj_commute)
              apply (rule verit_and_neg)
              apply (frule l_is_inr[of _ _ _ pick "pick'"])
               apply assumption
              apply (erule exE)
              apply hypsubst
              apply (subst sum.case)+
              apply (rule exI)+
              apply (drule r_is_Umap)
               apply (rule refl)
              apply hypsubst
              apply (unfold sum.case)
              apply (rule conjI[rotated])+
                  apply (rule refl)+
                prefer 3
                apply (drule valid_pick_set3[rotated])
                  apply assumption
                 apply (rule p)
                apply (unfold pred_sum_inject)
                apply assumption
               apply (rule supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound | assumption)+
  apply (rule exI)+
  apply (rule conjI[rotated])+
      apply (rule refl)+
    apply (rule assms)+
  done

lemma f_alpha:
  assumes p: "suitable pick" and p': "suitable pick'" and valid_d: "valid_U d"
  shows "alpha_E (f pick d) (f pick' d)"
  by (rule f_swap_alpha[OF assms bij_id supp_id_bound, unfolded Eperm_raw_id raw_Umap_id[OF valid_d]])

lemma exists_suitable:
  "\<exists> pick. suitable pick"
  apply (unfold suitable_def)
  apply (rule choice)
  apply (rule allI)
  apply (subst ex_simps)
  apply (rule impI)
  apply (erule ex_in_conv[THEN iffD2, OF Utor_ne])
  done

lemma suitable_pick0:
  "suitable pick0"
  apply (unfold pick0_def)
  apply (rule someI_ex[OF exists_suitable])
  done
lemmas f0_low_level_simps = f_simps[of pick0, unfolded f0_def[symmetric]]

lemma f0_Utor_aux:
  assumes "X \<in> Utor d" and valid_d: "valid_U d"
  shows "alpha_E (f (\<lambda> d'. if d' = d then X else pick0 d') d)
                       (raw_E_ctor (GMAP id id (case_sum id f0) (case_sum id f0) X))"
    apply(subst f_simps)
    apply (subst if_P[OF refl])
    apply(rule alpha_E.intros[of id], (rule bij_id supp_id_bound id_on_id)+)
    apply (unfold G.mr_rel_id[symmetric] G.rel_map)
    apply(rule G.rel_refl_strong)
(* REPEAT *)
     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
      apply (unfold sum.simps)
      apply (unfold Eperm_raw_id id_apply)?
      apply (rule alpha_refls)
      apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_def)?
     apply (rule f_alpha[OF _ suitable_pick0])

(* BLOCK: SUITABLE *)
     apply (unfold suitable_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable_def, THEN spec, THEN mp])
    apply assumption
   apply (rule assms(1)[unfolded Utor_def, THEN imageE])
   apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) G.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI1)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
  apply (rule assms)
  
(* END BLOCK *)

(* REPEATED, except UnI2 instead of UnI1 *)
  apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
      apply (unfold sum.simps)
      apply (unfold Eperm_raw_id id_apply)?
      apply (rule alpha_refls)
      apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_def)?
     apply (rule f_alpha[OF _ suitable_pick0])

     apply (unfold suitable_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable_def, THEN spec, THEN mp])
    apply assumption
   apply (rule assms(1)[unfolded Utor_def, THEN imageE])
   apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) G.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI2)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
  apply (rule assms)

(* END REPEAT *)
    done

lemma f0_Utor:
  assumes "X \<in> Utor d" "valid_U d"
  shows "alpha_E (f0 d) (raw_E_ctor (GMAP id id (case_sum id f0) (case_sum id f0) X))"
    apply (rule alpha_trans[rotated])
    apply (rule f0_Utor_aux[OF assms])
    apply (rule f_alpha[OF suitable_pick0 _ assms(2), unfolded f0_def[symmetric]])

(* BLOCK: SUITABLE *)
     apply (unfold suitable_def)
  apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable_def, THEN spec, THEN mp])
     apply assumption
(* END BLOCK *)
  done

lemma f0_mapD:
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a::covar_G set|" "valid_U d"
  shows "alpha_E (f0 (raw_Umap u d)) (Eperm_raw u (f0 d))"
  by (rule alpha_syms[OF f_swap_alpha[OF suitable_pick0 suitable_pick0 assms(3,1,2), unfolded f0_def[symmetric]]])

lemmas f0_FVarsD = f_FVarsD[OF suitable_pick0, unfolded f0_def[symmetric]]


(* The following theorems for raw theorems will now be lifted to quotiented Es: *)
thm f0_Utor f0_mapD f0_FVarsD


(*******************)
(* End product: *)

theorem COREC_DDTOR:
  assumes "X \<in> Udtor d" "valid_U d"
  shows "COREC d = E_ctor (GMAP id id (case_sum id COREC) (case_sum id COREC) X)"
  apply (unfold COREC_def E_ctor_def)
  apply (unfold o_def[symmetric])
  apply (subst G.map_comp, (rule supp_id_bound bij_id)+)
  apply (unfold E_total_abs_eq_iffs)
  apply (unfold o_case_sum)
  apply (unfold id_comp comp_id)
  apply (rule alpha_trans)
   apply (rule arg_cong[of _ _ "alpha_E (f0 d)", THEN iffD1])
    prefer 2
    apply (rule f0_Utor)
    apply (unfold Utor_def)
    apply (rule imageI)
     apply (rule assms)+
   apply (subst G.map_comp, (rule supp_id_bound bij_id)+)
   apply (unfold case_sum_o_map_sum)
   apply (unfold id_comp comp_id)
   apply (rule refl)
  apply(rule alpha_E.intros[of id], (rule bij_id supp_id_bound)+)
   apply (rule id_on_id)
  apply (unfold G.mr_rel_id[symmetric] G.rel_map)
  apply(rule G.rel_refl_strong)
   prefer 2
   apply (rule sumE)
    apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
     apply assumption
    apply hypsubst
    apply (unfold sum.simps)
    apply (rule alpha_refls)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold comp_apply)
   apply (rule E_rep_abs_syms)

  apply (rule sumE)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold Eperm_raw_id)
   apply (rule alpha_refls)
  apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
   apply assumption
  apply hypsubst
  apply (unfold sum.simps)
  apply (rule E_rep_abs_syms)
  done

lemma COREC_mmapD:
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a::covar_G set|" and "valid_U d"
  shows "COREC (Umap u d) = Eperm u (COREC d)"
  apply (unfold COREC_def Eperm_def)
  apply (unfold E_total_abs_eq_iffs)
  apply (rule alpha_trans)
   apply (rule f0_mapD[OF assms])
  apply (unfold alpha_bij_eqs[OF assms(1,2)])
  apply (rule alpha_syms)
  apply (rule E_rep_abs)
  done

theorem COREC_FFVarsD:
  "valid_U d \<Longrightarrow> EVrs (COREC d) \<subseteq> UFVars d"
  apply (unfold COREC_def EVrs_def alpha_FVars[OF E_rep_abs])
  apply (erule f0_FVarsD)
  done

end


lemmas EVrs_bound[simp] = E.FVars_bd_UNIVs

lemma GVrs2_bound[simp]: "|GVrs2 (u::('a :: covar_G, 'a, 'a E, 'a E) G)| <o |UNIV :: 'a set|"
  by (rule ordLess_ordLeq_trans[OF G.Vrs_bd(2) large'])

lemma Ector_fresh_inject:
  assumes "GVrs2 x \<inter> A = {}" "GVrs2 y \<inter> A = {}" "|A :: 'a::covar_G set| <o |UNIV :: 'a set|"
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

lemma permute_\<rho>:
  "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> |SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> = {} \<Longrightarrow> Eperm f (\<rho> a) = \<rho> (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho> a = Ector (\<eta> a)")
    apply (simp add: GMAP_def Gren_def eta_natural Eperm_Ector)
   apply simp
   apply (rule E.permute_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
    apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho> a = Ector (\<eta> a)")
   apply (simp add: GMAP_def Gren_def eta_natural Eperm_Ector)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done

lemma permute_\<rho>':
  "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> |SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>' = {} \<Longrightarrow> Eperm f (\<rho>' a) = \<rho>' (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho>' a = Ector (\<eta>' a)")
    apply (simp add: GMAP_def Gren_def eta'_natural Eperm_Ector)
   apply simp
   apply (rule E.permute_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
    apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho>' a = Ector (\<eta>' a)")
   apply (simp add: GMAP_def Gren_def eta'_natural Eperm_Ector)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done

abbreviation "IMSUPP \<delta> \<rho> \<rho>' \<equiv> imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'"
abbreviation "small_support \<delta> \<rho> \<rho>' \<equiv>
  |supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set| \<and>
  |SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set| \<and>
  |SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"

lemma small_IMSUPP: "small_support (\<delta> :: 'a \<Rightarrow> 'a :: covar_G) \<rho> \<rho>' \<Longrightarrow> |IMSUPP \<delta> \<rho> \<rho>'| <o |UNIV :: 'a set|"
  by (simp add: G.Un_bound imsupp_supp_bound)

abbreviation "DTOR \<equiv> (\<lambda>\<delta> \<rho> \<rho>' e. {u. Ector u = e \<and> GVrs2 u \<inter> IMSUPP \<delta> \<rho> \<rho>' = {}})"

lemma SSupp_Eperm_comp: 
  "bij (\<sigma> :: 'a \<Rightarrow> 'a::covar_G) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> SSupp (Ector \<circ> \<eta>) (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>) \<subseteq> SSupp (Ector \<circ> \<eta>) \<rho> \<union> supp \<sigma>"
  "bij (\<sigma> :: 'a \<Rightarrow> 'a::covar_G) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> SSupp (Ector \<circ> \<eta>') (Eperm \<sigma> \<circ> \<rho>' \<circ> inv \<sigma>) \<subseteq> SSupp (Ector \<circ> \<eta>') \<rho>' \<union> supp \<sigma>"
  apply (auto simp: SSupp_def imsupp_def image_iff)
  apply (metis Eperm_Ector Gren_def bij_imp_inv eta_natural not_in_supp_alt)
  apply (metis Eperm_Ector Gren_def bij_imp_inv eta'_natural not_in_supp_alt)
  done

interpretation Esub: COREC
  "\<lambda>(\<delta>, \<rho>, \<rho>', e). (if \<exists>a. e = Ector (\<eta> a) then GMAP id id Inl Inl ` DTOR \<delta> \<rho> \<rho>' (\<rho> (SOME a. e = Ector (\<eta> a)))
     else if \<exists>a. e = Ector (\<eta>' a) then GMAP id id Inl Inl ` DTOR \<delta> \<rho> \<rho>' (\<rho>' (SOME a. e = Ector (\<eta>' a)))
     else GMAP \<delta> id (\<lambda>u. Inr (\<delta>, \<rho>, \<rho>', u)) (\<lambda>u. Inr (\<delta>, \<rho>, \<rho>', u)) ` DTOR \<delta> \<rho> \<rho>' e)"
  "\<lambda>\<sigma> (\<delta>, \<rho>, \<rho>', e). (\<sigma> o \<delta> o inv \<sigma>, Eperm \<sigma> o \<rho> o inv \<sigma>, Eperm \<sigma> o \<rho>' o inv \<sigma>, Eperm \<sigma> e)"
  "\<lambda>(\<delta>, \<rho>, \<rho>', e). EVrs e \<union> IMSUPP \<delta> \<rho> \<rho>'"
  "\<lambda>(\<delta>, \<rho>, \<rho>', e). small_support \<delta> \<rho> \<rho>'"
  apply standard
  subgoal for d
    apply (auto intro!: Un_bound simp: imsupp_supp_bound
        Ector_eta_inj Ector_eta_inj' eta_distinct' split: if_splits) []
      apply (metis E.TT_fresh_cases small_IMSUPP)
     apply (metis E.TT_fresh_cases small_IMSUPP)
    apply (metis E.TT_fresh_cases small_IMSUPP)
    done
  subgoal for X X' d
    apply (auto split: if_splits simp: map_sum_o_inj GMAP_def Gren_def 
      G.Map_Sb[THEN fun_cong, simplified]
      G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
      G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj
      Ector_eta_inj Ector_eta_inj' Ector_eta'_inj Ector_eta'_inj' eta_inject eta'_inject)
    subgoal for \<delta> \<rho> \<rho>' a u u'
      apply (subgoal_tac "Ector u' = Ector u")
       apply (subst (asm) Ector_fresh_inject[where A="IMSUPP \<delta> \<rho> \<rho>'"])
          apply blast
         apply blast
        apply (blast intro: small_IMSUPP)
       apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (rule exI[of _ \<sigma>])
        apply (auto simp: Gren_def 
            G.Map_Sb[THEN fun_cong, simplified]
            G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified])
        done
      apply simp
      done
    subgoal for \<delta> \<rho> \<rho>' a u u'
      apply (subgoal_tac "Ector u = Ector u'")
       apply (subst (asm) Ector_fresh_inject[where A="IMSUPP \<delta> \<rho> \<rho>'"])
          apply blast
         apply blast
        apply (blast intro: small_IMSUPP)
       apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (rule exI[of _ \<sigma>])
        apply (auto simp: Gren_def 
            G.Map_Sb[THEN fun_cong, simplified]
            G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified])
        done
      apply simp
      done
    subgoal for \<delta> \<rho> \<rho>' u u'
      apply (drule sym[of "Ector u'"])
       apply (subst (asm) Ector_fresh_inject[where A="IMSUPP \<delta> \<rho> \<rho>'"])
          apply blast
         apply blast
        apply (blast intro: small_IMSUPP)
       apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (rule exI[of _ \<sigma>])
        apply (auto simp: Gren_def comp_def
            permute_\<rho> permute_\<rho>' imsupp_commute[THEN fun_cong, simplified, of \<sigma> \<delta>] Int_Un_distrib
            G.Map_Sb[THEN fun_cong, simplified]
            G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified])
        done
      done
    subgoal for \<delta> \<rho> \<rho>' u u'
      apply (drule sym[of "Ector u'"])
       apply (subst (asm) Ector_fresh_inject[where A="IMSUPP \<delta> \<rho> \<rho>'"])
          apply blast
         apply blast
        apply (blast intro: small_IMSUPP)
       apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (drule spec[of _ \<sigma>])
        apply (auto simp: Gren_def comp_def G.Vrs_Sb G.Vrs_Map
            permute_\<rho> permute_\<rho>' imsupp_commute[THEN fun_cong, simplified, of \<sigma> \<delta>] Int_Un_distrib
            G.Map_Sb[THEN fun_cong, simplified]
            G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified])
         apply (erule notE)
        apply (smt (verit, ccfv_threshold) Diff_iff Int_emptyD Un_iff id_on_def
            not_in_imsupp_same)
        apply (meson not_ordLeq_ordLess)
        done
      done
    done
  subgoal for d X
    apply (auto  simp: map_sum_o_inj GMAP_def Gren_def EVrs_Ector
      G.Map_Sb[THEN fun_cong, simplified]
      G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
      G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj
      Ector_eta_inj Ector_eta_inj' Ector_eta'_inj Ector_eta'_inj' eta_inject eta'_inject
      split: if_splits)
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho> b = Ector (\<eta> b)")
       apply (simp add: Ector_eta_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho>' b = Ector (\<eta>' b)")
       apply (simp add: Ector_eta'_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
         apply (metis in_imsupp not_in_imsupp_same)
        apply (metis in_imsupp not_in_imsupp_same)
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho> b = Ector (\<eta> b)")
       apply (simp add: Ector_eta_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho>' b = Ector (\<eta>' b)")
       apply (simp add: Ector_eta'_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho> b = Ector (\<eta> b)")
       apply (simp add: Ector_eta_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho>' b = Ector (\<eta>' b)")
       apply (simp add: Ector_eta'_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    done
  subgoal for \<sigma> d
    apply (auto split: if_splits simp: map_sum_o_inj GMAP_def Gren_def Eperm_Ector
      G.Map_Sb[THEN fun_cong, simplified]
      G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
      G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj
      Ector_eta_inj Ector_eta_inj' Ector_eta'_inj Ector_eta'_inj' eta_inject eta'_inject
      eta_natural eta'_natural eta_distinct eta_distinct' image_image)
        apply (rule image_eqI[rotated])
         apply (rule CollectI)
         apply (rule conjI)
    sorry
  subgoal
    by (auto simp: Eperm_comp[THEN fun_cong, simplified] fun_eq_iff o_inv_distrib)
  subgoal for d \<sigma>
    apply (auto intro!: Eperm_cong_id simp: fun_eq_iff)
    apply (metis in_imsupp inv_simp1 inv_simp2 not_in_imsupp_same)
    apply (metis (no_types, lifting) Int_emptyI bij_id_imsupp inv_simp2 permute_\<rho>)
    apply (metis (no_types, lifting) Int_emptyI bij_id_imsupp inv_simp2 permute_\<rho>')
    done
  subgoal for \<sigma> d
    apply (auto simp: supp_comp_bound Un_bound
      intro!: ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_Eperm_comp(1)]]
              ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_Eperm_comp(2)]])
    done
  subgoal for d u
    apply (auto simp: map_sum_o_inj GMAP_def Gren_def G.pred_set
      G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj
      Ector_eta_inj Ector_eta_inj' Ector_eta'_inj Ector_eta'_inj' eta_inject eta'_inject
      split: if_splits)
    done
  done

definition "Esub \<delta> \<rho> \<rho>' e = Esub.COREC (\<delta>, \<rho>, \<rho>', e)"

lemma
  assumes
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  shows
  Esub_Ector\<eta>: "Esub \<delta> \<rho> \<rho>' (Ector (\<eta> a)) = \<rho> a"
  and Esub_Ector\<eta>': "Esub \<delta> \<rho> \<rho>' (Ector (\<eta>' a)) = \<rho>' a"
  and Esub_Ector:
  "GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
   GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  Esub \<delta> \<rho> \<rho>' (Ector u) = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u))"
    apply -
  unfolding Esub_def
  subgoal
    apply (insert Ector_fresh_surj[of "IMSUPP \<delta> \<rho> \<rho>'" "\<rho> a"])
    apply (drule meta_mp)
     apply (simp add: assms small_IMSUPP)
    apply (erule exE)
    subgoal for u
    apply (subst Esub.COREC_DDTOR[of "GMAP id id Inl Inl u"])
      apply (auto simp: assms case_sum_o_inj Ector_eta_inj
          G.Map_Sb[THEN fun_cong, simplified]
          G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
          G.Sb_Inj G.Map_id GMAP_def Gren_def eta_inject)
      done
    done
  subgoal
    apply (insert Ector_fresh_surj[of "IMSUPP \<delta> \<rho> \<rho>'" "\<rho>' a"])
    apply (drule meta_mp)
     apply (simp add: assms small_IMSUPP)
    apply (erule exE)
    subgoal for u
    apply (subst Esub.COREC_DDTOR[of "GMAP id id Inl Inl u"])
      apply (auto simp: assms case_sum_o_inj Ector_eta'_inj'
          G.Map_Sb[THEN fun_cong, simplified]
          G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
          G.Sb_Inj G.Map_id GMAP_def Gren_def eta_distinct eta'_inject)
      done
    done
  subgoal
    apply (subst Esub.COREC_DDTOR[of "GMAP \<delta> id (\<lambda>e. Inr (\<delta>, \<rho>, \<rho>', e)) (\<lambda>e. Inr (\<delta>, \<rho>, \<rho>', e)) u"])
    using assms
      apply (auto simp: case_sum_o_inj comp_def Ector_eta_inj Ector_eta'_inj
          G.Map_Sb[THEN fun_cong, simplified]
          G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
          G.Sb_Inj G.Map_id GMAP_def Gren_def eta_distinct eta'_inject)
    done
  done

lemma EVrs_Esub:
  assumes
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  shows "EVrs (Esub \<delta> \<rho> \<rho>' e)
    \<subseteq> EVrs e \<union> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>')"
  unfolding Esub_def
  apply (rule order_trans[OF Esub.COREC_FFVarsD])
   apply (auto simp: assms)
  done

lemma Eperm_Esub:
  assumes
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  shows "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
  imsupp f \<inter> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>') = {} \<Longrightarrow>
  Eperm f (Esub \<delta> \<rho> \<rho>' t) = Esub \<delta> \<rho> \<rho>' (Eperm f t)"
  using assms unfolding Esub_def
  apply (subst Esub.COREC_mmapD[symmetric])
     apply auto [3]
  apply (rule arg_cong[where f = Esub.COREC])
  apply (auto simp add: fun_eq_iff Int_Un_distrib permute_\<rho> permute_\<rho>' imsupp_commute)
  done

lemma Esub_inversion0:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
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
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
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
  assumes "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "SSupp (Ector \<circ> \<eta>) (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'') \<subseteq>
   SSupp (Ector \<circ> \<eta>) \<rho>'' \<union> SSupp (Ector \<circ> \<eta>) \<rho>"
    "SSupp (Ector \<circ> \<eta>') (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'') \<subseteq>
   SSupp (Ector \<circ> \<eta>') \<rho>'' \<union> SSupp (Ector \<circ> \<eta>') \<rho>'"
  using assms
  by (auto simp: SSupp_def Esub_Ector\<eta> Esub_Ector\<eta>')

lemma SSupp_comp_bound[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>''| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'')| <o |UNIV :: 'a set|"
  apply (rule ordLeq_ordLess_trans)
   apply (erule (2) card_of_mono1[OF SSupp_comp_Esub_le(1)])
  apply (auto simp: Un_bound)
  done

lemma SSupp_comp_bound'[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set| \<Longrightarrow>
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
  "|EFVrs (x :: 'a :: covar_G E)| <o card_suc Gbd"
  "|EFVrs\<eta> (x :: 'a :: covar_G E)| <o card_suc Gbd"
  "|EFVrs\<eta>' (x :: 'a :: covar_G E)| <o card_suc Gbd"
    apply (meson EVrs_bd Efree_alt(1) Efreee_Efree card_of_subset_bound subset_eq)
   apply (meson EVrs_bd Efree_alt(2) Efree\<eta>_Efree card_of_subset_bound subset_eq)
  apply (meson EVrs_bd Efree_alt(3) Efree\<eta>'_Efree card_of_subset_bound subset_eq)
  done

lemma EFVrs_bound[simp]:
  "|EFVrs (x :: 'a :: covar_G E)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta> (x :: 'a :: covar_G E)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta>' (x :: 'a :: covar_G E)| <o |UNIV :: 'a set|"
  using EFVrs_bd large' ordLess_ordLeq_trans by blast+

lemma EFVrs_EsubI1[OF _ _ _ _ refl]:
  assumes
    "z \<in> EFVrs e"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::covar_G)| <o |UNIV :: 'a set|"
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
pbmv_monad "'a::covar_G E"
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
       |supp (f :: 'a :: covar_G \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
       Esub f \<rho>1 \<rho>2 \<circ> (Ector \<circ> \<eta>) = \<rho>1"
 "\<And>f \<rho>1 \<rho>2.
       |supp (f :: 'a :: covar_G \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
       Esub f \<rho>1 \<rho>2 \<circ> (Ector \<circ> \<eta>') = \<rho>2"
 "\<And>g \<rho>'1 \<rho>'2 f \<rho>1 \<rho>2.
       |supp (f :: 'a :: covar_G \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
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
        |supp (f :: 'a :: covar_G \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs (Esub f \<rho>1 \<rho>2 x) =
        f ` EFVrs x \<union>
        ((\<Union>x\<in>EFVrs\<eta> x. EFVrs (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs (\<rho>2 x)))"
 "\<And>f \<rho>1 \<rho>2 x.
        |supp (f :: 'a :: covar_G \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs\<eta> (Esub f \<rho>1 \<rho>2 x) =
        (\<Union>x\<in>EFVrs\<eta> x. EFVrs\<eta> (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs\<eta> (\<rho>2 x))"
 "\<And>f \<rho>1 \<rho>2 x.
        |supp (f :: 'a :: covar_G \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs\<eta>' (Esub f \<rho>1 \<rho>2 x) =
        (\<Union>x\<in>EFVrs\<eta> x. EFVrs\<eta>' (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs\<eta>' (\<rho>2 x))"
 "\<And>f \<rho>1 \<rho>2 g \<rho>'1 \<rho>'2 x.
        |supp (f :: 'a :: covar_G \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
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