theory MRBNF_Recursor
  imports MRBNF_FP
  keywords "binder_datatype" :: thy_defn
    and "binder_inductive" :: thy_goal_defn
    and "make_binder_inductive" :: thy_goal_defn
    and "binds"
begin

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

ML_file \<open>../Tools/mrbnf_tvsubst.ML\<close>
ML_file \<open>../Tools/mrbnf_sugar.ML\<close>

declare [[inductive_internals]]

context begin
ML_file \<open>../Tools/binder_induction.ML\<close>
end
ML_file \<open>../Tools/binder_inductive.ML\<close>
ML_file \<open>../Tools/binder_inductive_combined.ML\<close>

typedecl ('a, 'b) var_selector (infix "::" 999)

ML_file "../Tools/parser.ML"

end