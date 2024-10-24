theory MRBNF_Recursor
  imports MRBNF_FP
  keywords "binder_datatype" :: thy_defn
    and "binder_inductive" :: thy_goal_defn
    and "binds"
begin

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

ML_file \<open>../Tools/mrbnf_tvsubst.ML\<close>
ML_file \<open>../Tools/mrbnf_sugar.ML\<close>

named_theorems equiv
named_theorems equiv_commute
named_theorems equiv_simps

declare Un_iff[equiv_simps] de_Morgan_disj[equiv_simps]
  inj_image_mem_iff[OF bij_is_inj, equiv_simps]
  singleton_iff[equiv_simps] image_empty[equiv_simps]
  Int_Un_distrib[equiv_simps] Un_empty[equiv_simps]
  image_is_empty[equiv_simps] image_Int[OF bij_is_inj, symmetric, equiv_simps]
  inj_eq[OF bij_is_inj, equiv_simps] inj_eq[OF bij_is_inj, equiv_simps]
  image_insert[equiv_simps] insert_iff[equiv_simps] notin_empty_eq_True[equiv_simps]

context begin
ML_file \<open>../Tools/binder_induction.ML\<close>
end
ML_file \<open>../Tools/binder_inductive.ML\<close>

typedecl ('a, 'b) var_selector (infix "::" 999)

ML_file "../Tools/parser.ML"

end