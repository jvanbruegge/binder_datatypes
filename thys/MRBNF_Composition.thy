theory MRBNF_Composition
  imports Prelim
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal
begin

ML_file \<open>../Tools/mrbnf_util.ML\<close>
ML_file \<open>../Tools/mrbnf_def_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_def.ML\<close>

local_setup \<open>snd o MRBNF_Def.register_bnf_as_mrbnf (SOME "BNF_Composition.ID") (BNF_Comp.ID_bnf)\<close>
local_setup \<open>snd o MRBNF_Def.register_bnf_as_mrbnf (SOME "BNF_Composition.DEADID") (BNF_Comp.DEADID_bnf)\<close>

lemma Grp_Rep: "type_definition Rep Abs top \<Longrightarrow> type_definition Rep2 Abs2 top \<Longrightarrow>
  ((BNF_Def.Grp (Collect P) f)\<inverse>\<inverse> OO BNF_Def.Grp (Collect P) g) (Rep x) (Rep2 y) =
  ((BNF_Def.Grp (Collect P) (Abs \<circ> f))\<inverse>\<inverse> OO BNF_Def.Grp (Collect P) (Abs2 \<circ> g)) x y"
  unfolding relcompp_apply Grp_def conversep_def
  by (metis comp_def iso_tuple_UNIV_I type_definition_def)
lemma type_copy_vimage2p_Grp_Rep_id: "type_definition Rep Abs UNIV \<Longrightarrow> BNF_Def.vimage2p id Rep (BNF_Def.Grp (Collect P) h) = BNF_Def.Grp {x. P x} (Abs \<circ> h)"
  using type_copy_vimage2p_Grp_Rep[of _ _ id]
  by auto
lemma type_definition_id: "type_definition id id top"
  unfolding type_definition_def
  by simp

lemma image_single: "{f x} = f ` {x}"
  by simp

ML_file \<open>../Tools/mrbnf_comp_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_comp.ML\<close>

end
