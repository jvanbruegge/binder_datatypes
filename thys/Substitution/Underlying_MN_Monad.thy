theory Underlying_MN_Monad
imports Preliminaries 
begin

(**************************)
(* The starting MN-monad / pre-(co)datatype *)
(* Our G stands for G0 in the 
triple (I0,P0,G0), where:  
--- I0 = {1,2} (two variable kinds, represented by the first 
two Isabelle type-variables 'a1 and 'a2 of ('a1,'a2,'c1,'c2)G);
--- P0 = {1,2} (two parameter kinds, represented by the first 
two Isabelle type-variables 'c1 and 'c2 of ('a1,'a2,'c1,'c2)G).
*)

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

lemma Gmap_comp: 
"Gmap g1 g2 (Gmap f1 f2 u) = Gmap (g1 \<circ> f1) (g2 \<circ> f2) u"
by (metis G.Map_comp comp_apply)

lemmas GVrs1_Gmap = G.Vrs_Map1
lemmas GVrs2_Gmap = G.Vrs_Map2
lemmas GSupp1_Gmap = G.Supp1_Map
lemmas GSupp2_Gmap = G.Supp2_Map
lemmas Gmap_cong = G.Map_cong
lemmas Gsub_cong = G.Sb_cong
lemmas Gsub_id = G.Sb_Inj
lemmas Gsub_comp = G.Sb_comp
lemmas Gsub_comp' = Gsub_comp[symmetric, unfolded fun_eq_iff, 
rule_format, simplified]

lemmas Gsub_cong_id = Gsub_cong[of _ _ id id, 
unfolded Gsub_id, 
simplified]

lemmas Gren_cong = Gsub_cong[unfolded Gren_def[symmetric]]
lemmas Gren_cong_id = Gsub_cong_id[unfolded Gren_def[symmetric]]
lemmas Gren_comp = Gsub_comp[unfolded Gren_def[symmetric]]
lemmas Gren_comp' = Gsub_comp'[unfolded Gren_def[symmetric]]
lemmas Gren_id = Gsub_id[unfolded Gren_def[symmetric]]

end 