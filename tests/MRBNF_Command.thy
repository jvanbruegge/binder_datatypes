theory MRBNF_Command
  imports "../thys/MRBNF_Recursor" "HOL-Library.Stream"
begin

class external =
  assumes large: "|Field bd_stream| \<le>o |UNIV::'a set|" and regular: "regularCard |UNIV::'a set|"

lemma infinite_natLeq: "natLeq \<le>o |A| \<Longrightarrow> infinite A"
  using infinite_iff_natLeq_ordLeq by blast

lemma (in external) infinite: "infinite (UNIV :: 'a set)"
  apply (rule infinite_natLeq)
  apply (rule ordLeq_transitive)
   prefer 2
   apply (rule large)
  apply (rule ordLeq_ordIso_trans)
   prefer 2
   apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
   apply (tactic \<open>resolve_tac @{context} [BNF_Def.bd_Card_order_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name stream}))] 1\<close>)
  apply (rule natLeq_ordLeq_cinfinite)
  apply (tactic \<open>resolve_tac @{context} [BNF_Def.bd_Cinfinite_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name stream}))] 1\<close>)
  done

mrbnf "'a stream"
map: smap
sets:
  live: sset
bd: bd_stream
rel: stream_all2
pred: pred_stream
var_class: external
  sorry

end