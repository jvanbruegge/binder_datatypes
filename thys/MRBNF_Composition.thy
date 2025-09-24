theory MRBNF_Composition
  imports "Prelim.Prelim"
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal (*and
    "linearize_mrbnf" :: thy_goal*)
begin

ML_file \<open>../Tools/mrbnf_util.ML\<close>
ML_file \<open>../Tools/mrbnf_def_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_def.ML\<close>

local_setup \<open>snd o MRBNF_Def.register_bnf_as_mrbnf (SOME "BNF_Composition.ID") (BNF_Comp.ID_bnf)\<close>
local_setup \<open>snd o MRBNF_Def.register_bnf_as_mrbnf (SOME "BNF_Composition.DEADID") (BNF_Comp.DEADID_bnf)\<close>

local_setup \<open>fold (fn name => fn lthy =>
  snd (MRBNF_Def.register_bnf_as_mrbnf NONE (the (BNF_Def.bnf_of lthy name)) lthy)
) [@{type_name sum}, @{type_name prod}]
\<close>

lemma type_copy_vimage2p_Grp_Rep_UNIV:
   assumes "type_definition Rep Abs UNIV"
  shows "BNF_Def.vimage2p f Rep (Grp h) = Grp (Abs \<circ> h \<circ> f)"
  unfolding vimage2p_def Grp_def fun_eq_iff
  by (auto simp: type_definition.Abs_inverse[OF assms UNIV_I]
   type_definition.Rep_inverse[OF assms] dest: sym)

lemma Grp_Rep: "type_definition Rep Abs top \<Longrightarrow> type_definition Rep2 Abs2 top \<Longrightarrow>
  ((BNF_Def.Grp A f)\<inverse>\<inverse> OO BNF_Def.Grp B g) (Rep x) (Rep2 y) =
  ((BNF_Def.Grp A (Abs \<circ> f))\<inverse>\<inverse> OO BNF_Def.Grp B (Abs2 \<circ> g)) x y"
  unfolding relcompp_apply Grp_def conversep_def
  by (metis comp_def iso_tuple_UNIV_I type_definition_def)
lemma type_copy_vimage2p_Grp_Rep_id:
  assumes type_copy: "type_definition Rep Abs UNIV"
  shows "BNF_Def.vimage2p id Rep (BNF_Def.Grp A h) = BNF_Def.Grp A (Abs \<circ> h)"
  unfolding vimage2p_def Grp_def fun_eq_iff
  by (auto simp: type_definition.Abs_inverse[OF type_copy UNIV_I]
   type_definition.Rep_inverse[OF type_copy] dest: sym)
lemma type_definition_id: "type_definition id id top"
  unfolding type_definition_def
  by simp

lemma image_single: "{f x} = f ` {x}"
  by simp

lemma Grp_OO: "(Grp f OO R) x y = R (f x) y"
  unfolding OO_def Grp_UNIV_def by blast

lemma Grp_OO_top: "(Grp g OO top) = top"
  by (auto simp: Grp_def)

ML_file \<open>../Tools/mrbnf_comp_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_comp.ML\<close>


(* linearize_mrbnf command
definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV :: 'a set| then f else id"

ML_file "../Tools/mrbnf_linearize_tactics.ML"
ML_file "../Tools/mrbnf_linearize.ML" *)

end
