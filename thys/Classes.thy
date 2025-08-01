theory Classes
  imports "Prelim.Prelim"
begin

lemma Cinfinite_ordLeq_natLeq: "Cinfinite r \<Longrightarrow> |Field natLeq| \<le>o r"
  using card_of_least natLeq_Well_order natLeq_ordLeq_cinfinite ordLeq_transitive by blast

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
  assumes large: "cardSuc natLeq \<le>o |UNIV::'a set|"
    and regular: "regularCard |UNIV::'a set|"

subclass (in covar) var
  apply standard
   apply (metis Field_natLeq infinite_iff_card_of_nat infinite_iff_natLeq_ordLeq le_card_ivar local.large ordLeq_transitive ordLess_imp_ordLeq)
  by (rule local.regular)

ML_file \<open>../Tools/var_classes.ML\<close>

local_setup \<open>
   Var_Classes.register_class_for_bound @{class var} @{term natLeq}
#> Var_Classes.register_class_for_bound @{class covar} @{term "cardSuc natLeq"}
\<close>

end