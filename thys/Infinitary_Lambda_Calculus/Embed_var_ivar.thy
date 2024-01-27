theory Embed_var_ivar
imports Untyped_Lambda_Calculus.LC ILC
begin

(* and embedding of vars to ivars: *)

lemma card_var_ivar: "|UNIV::var set| <o |UNIV::ivar set|" 
using card_var natLeq_less_UNIV ordIso_ordLess_trans by blast

definition ivarOf :: "var \<Rightarrow> ivar" where "ivarOf \<equiv> ILC.embed"

lemma ivarOf_inj: "inj ivarOf"
unfolding ivarOf_def by (metis inj_embed)

lemma inj_ivarOf[simp]: "ivarOf n = ivarOf m \<longleftrightarrow> n = m"
by (meson injD ivarOf_inj)


end 