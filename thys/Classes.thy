theory Classes
  imports "Prelim.Prelim" Support
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

lemma (in infinite) single_bound[simp]: "|{x}| <o |UNIV::'a set|"
  by (simp add: local.infinite_UNIV)

lemmas [simp] = infinite_UNIV

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
  apply (simp add: Cinfinite_ordLeq_natLeq cinfinite_iff_infinite)
  using list_countable natLeq_Cinfinite ordIso_symmetric regularCard_natLeq regularCard_ordIso by blast
end

(********* covar class **************)
class covar =
  assumes large: "|Field (card_suc natLeq)| \<le>o |UNIV::'a set|"
    and regular: "regularCard |UNIV::'a set|"

lemma (in covar) large': "card_suc natLeq \<le>o |UNIV::'a set|"
  by (metis Card_order_iff_ordLeq_card_of Field_card_suc cset.bd_card_order local.large ordLeq_transitive)

subclass (in covar) var
  apply standard
  using Cinfinite_ordLeq_natLeq cinfinite_mono cset.bd_cinfinite local.large' apply blast
  by (rule local.regular)

lemma cinfinite_wit: "cinfinite r \<Longrightarrow> \<exists>x. x \<in> Field r"
  by (metis cinfinite_def equals0I finite.emptyI)

typedef wit_covar = "Field (card_suc natLeq)"
  by (simp add: Field_card_suc)

instantiation wit_covar :: covar
begin
instance
  apply standard
   apply (rule ordLeq_ordIso_trans[OF _ type_definition_card_UNIV[OF type_definition_wit_covar]])
   apply (rule ordLeq_refl)
   apply (rule card_of_Card_order)
  apply (rule regularCard_ordIso[OF ordIso_transitive[OF ordIso_symmetric[OF card_of_Field_ordIso] type_definition_card_UNIV[OF type_definition_wit_covar]]])
    apply (simp add: Field_card_suc cset.bd_card_order)
   apply (simp add: Field_card_suc cset.bd_card_order cset.bd_cinfinite)
  by (simp add: cset.bd_regularCard)
end

ML_file \<open>../Tools/var_classes.ML\<close>

local_setup \<open>
   Var_Classes.register_class_for_bound @{class var} @{term natLeq}
#> Var_Classes.register_class_for_bound @{class covar} @{term "card_suc natLeq"}
\<close>


(* Theorems *)
lemma supp_comp_bound_var:
  assumes bound: "|supp f| <o |UNIV::'a::infinite set|" "|supp g| <o |UNIV::'a set|"
  shows "|supp (g \<circ> f)| <o |UNIV::'a set|"
  using supp_comp_bound[OF assms] infinite_UNIV by blast

lemma insert_bound[simp]: "|insert x A| <o |UNIV::'a::infinite set| \<longleftrightarrow> |A| <o |UNIV::'a set|"
  by (metis card_of_Un_singl_ordLess_infinite infinite_UNIV insert_is_Un)

lemmas SSupp_comp_bound_UNIV[simp, intro!] = SSupp_comp_bound[OF conjI[OF var_class.UNIV_cinfinite card_of_Card_order]]

lemma IImsupp_Inj_comp_bound1: "inj Inj \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow>
   (\<And>a. Vrs (Inj a) = {a}) \<Longrightarrow> |IImsupp Inj Vrs (Inj \<circ> f)| <o |UNIV::'a set|"
  by (simp add: IImsupp_def UN_bound)

lemma IImsupp_Inj_comp_bound2: "(\<And>a. Vrs (Inj a) = {}) \<Longrightarrow> |IImsupp Inj Vrs (Inj \<circ> f)| <o |UNIV::'a set|"
  by (auto simp: IImsupp_def)

lemmas IImsupp_Inj_comp_bound = IImsupp_Inj_comp_bound1 IImsupp_Inj_comp_bound2

lemma SSupp_fun_upd_bound_UNIV[simp]: "|SSupp Inj (f(x := t))| <o |UNIV::'a::var set| \<longleftrightarrow> |SSupp Inj f| <o |UNIV::'a set|"
  by (simp add: UNIV_cinfinite)

lemma SSupp_fun_upd_Inj_bound[simp]: "|SSupp Inj (Inj(x := t))| <o |UNIV::'a::var set|"
  by simp

lemma IImsupp_fun_upd_Inj_bound[simp, intro!]: "(\<And>x. |Vrs x| <o |UNIV::'a::var set| ) \<Longrightarrow> |IImsupp Inj Vrs (Inj(x := t))| <o |UNIV::'a::var set|"
  unfolding IImsupp_def by (meson SSupp_fun_upd_Inj_bound UN_bound)

lemma supp_fun_upd_var: "|supp (id(v::'a::var := t))| <o |UNIV::'a set|"
  by (simp add: supp_def)

end
