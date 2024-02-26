theory MRBNF_Recursor
  imports MRBNF_FP
begin

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

ML_file \<open>../Tools/mrbnf_tvsubst.ML\<close>
ML_file \<open>../Tools/mrbnf_sugar.ML\<close>

context begin
ML_file \<open>../Tools/binder_induction.ML\<close>
end

end