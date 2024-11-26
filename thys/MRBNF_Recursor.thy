theory MRBNF_Recursor
  imports MRBNF_FP
  keywords "binder_datatype" :: thy_defn
    and "binder_inductive" :: thy_goal_defn
    and "binds"
begin

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

ML_file \<open>../Tools/mrbnf_tvsubst.ML\<close>
ML_file \<open>../Tools/mrbnf_sugar.ML\<close>

context begin
ML_file \<open>../Tools/binder_induction.ML\<close>
end
ML_file \<open>../Tools/binder_inductive.ML\<close>

typedecl ('a, 'b) var_selector

ML_file "../Tools/parser.ML"

end