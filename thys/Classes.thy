theory Classes
  imports "Prelim.Prelim"
begin

ML_file \<open>../Tools/mrbnf_util.ML\<close>

lemma Cinfinite_ordLeq_natLeq: "Cinfinite r \<Longrightarrow> |Field natLeq| \<le>o r"
  using card_of_least natLeq_Well_order natLeq_ordLeq_cinfinite ordLeq_transitive by blast

lemma type_copy_ordLeq_dir_image: "Card_order r \<Longrightarrow> type_definition Rep Abs UNIV \<Longrightarrow> r =o dir_image r Abs"
  apply (erule dir_image[rotated])
  apply (erule type_definition.Abs_inject)
   apply (rule UNIV_I)+
  done

lemma Card_order_dir_image: "Card_order r \<Longrightarrow> type_definition Rep Abs UNIV \<Longrightarrow> Card_order (dir_image r Abs)"
  using Card_order_ordIso2 type_copy_ordLeq_dir_image by blast

(********* infinite class ***********)
lemma (in infinite) Un_bound: "|A| <o |UNIV::'a set| \<Longrightarrow> |B| <o |UNIV::'a set| \<Longrightarrow> |A \<union> B| <o |UNIV::'a set|"
  using card_of_Un_ordLess_infinite local.infinite_UNIV by blast

(********* var class ****************)
class var =
  assumes large: "|Field natLeq| \<le>o |UNIV::'a set|"
    and regular: "regularCard |UNIV::'a set|"

lemma (in var) large': "natLeq \<le>o |UNIV::'a set|"
  using Field_natLeq card_of_ordLeq_finite infinite_iff_natLeq_ordLeq local.large by auto

lemma (in var) UNIV_cinfinite: "cinfinite |UNIV::'a set|"
  using Field_natLeq cinfinite_def infinite_iff_card_of_nat local.large by fastforce

lemma (in var) UN_bound: "|A| <o |UNIV::'a set| \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> |f x| <o |UNIV::'a set| ) \<Longrightarrow> |\<Union>(f ` A)| <o |UNIV::'a set|"
  using card_of_Card_order card_of_UNION_ordLess_infinite_Field cinfinite_def local.UNIV_cinfinite local.regular regularCard_stable by blast

subclass (in var) infinite
  apply standard
  using Field_natLeq infinite_iff_card_of_nat local.large by auto

instantiation nat::var begin
  instance by standard (auto simp: stable_nat stable_regularCard)
end

lemma list_countable: "|UNIV::('a::finite) list set| =o natLeq"
  by (meson card_of_nat countableI_type countable_or_card_of infinite_UNIV_listI ordIso_transitive)

instantiation list :: (finite) var begin
instance
  apply standard
  using Field_natLeq infinite_UNIV infinite_iff_card_of_nat apply auto[1]
  using list_countable natLeq_Cinfinite ordIso_symmetric regularCard_natLeq regularCard_ordIso by blast
end

(********* covar class **************)
class covar =
  assumes large: "|Field (cardSuc natLeq)| \<le>o |UNIV::'a set|"
    and regular: "regularCard |UNIV::'a set|"

lemma (in covar) large': "cardSuc natLeq \<le>o |UNIV::'a set|"
  using Card_order_iff_ordLeq_card_of cardSuc_Card_order local.large natLeq_Card_order ordLeq_transitive by blast

subclass (in covar) var
  apply standard
  apply (metis Cinfinite_ordLeq_natLeq Field_card_of cardSuc_ordLeq card_of_card_order_on cinfinite_mono local.large' natLeq_Cinfinite)
  by (rule local.regular)

lemma cinfinite_wit: "cinfinite r \<Longrightarrow> \<exists>x. x \<in> Field r"
  by (metis cinfinite_def equals0I finite.emptyI)

typedef wit_covar = "Field (cardSuc natLeq)"
  by (simp add: cinfinite_wit Cinfinite_cardSuc natLeq_Cinfinite)

instantiation wit_covar :: covar
begin
instance
  apply standard
   apply (rule ordLeq_ordIso_trans[OF _ type_definition_card_UNIV[OF type_definition_wit_covar]])
   apply (rule ordLeq_refl)
   apply (rule card_of_Card_order)
  apply (rule regularCard_ordIso[OF ordIso_transitive[OF ordIso_symmetric[OF card_of_Field_ordIso] type_definition_card_UNIV[OF type_definition_wit_covar]]])
    apply (simp add: natLeq_Cinfinite)
  using Cinfinite_cardSuc natLeq_Cinfinite apply blast
  by (simp add: natLeq_Cinfinite regularCard_cardSuc)
end

ML_file \<open>../Tools/var_classes.ML\<close>

local_setup \<open>
   Var_Classes.register_class_for_bound @{class var} @{term natLeq}
#> Var_Classes.register_class_for_bound @{class covar} @{term "cardSuc natLeq"}
\<close>

typedecl bdT
axiomatization bd :: "(bdT \<times> bdT) set" where
  Cinf: "Cinfinite bd"
  and regular: "regularCard bd"

local_setup \<open>fn lthy =>
let
  val (class, lthy) = Var_Classes.mk_class_for_bound @{binding var_bd} @{term bd} lthy;

  val lthy = Var_Classes.prove_class_theorems true true class @{thm Cinf} @{thm regular} lthy;
in lthy end
\<close>

end