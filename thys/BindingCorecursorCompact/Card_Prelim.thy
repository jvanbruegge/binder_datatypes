theory Card_Prelim 
imports "HOL-Cardinals.Cardinals" "HOL-Library.Countable" "HOL-Library.FuncSet"
begin

lemma countable_natLeq: "|UNIV::'a::countable set| \<le>o natLeq"  
proof -
  have "|UNIV::'a set| \<le>o |UNIV::nat set|"
  by (meson card_of_ordLeqI ex_inj iso_tuple_UNIV_I)
  then show ?thesis
  by (metis (full_types) Field_card_of Field_natLeq card_of_Well_order card_of_mono2 
       card_of_nat natLeq_Well_order not_ordLeq_iff_ordLess ordIso_transitive 
       ordLeq_iff_ordLess_or_ordIso)
qed

lemma countable_set_natLeq: "|I::'a::countable set| \<le>o natLeq" 
  using card_of_UNIV countable_natLeq ordLeq_transitive by blast

lemma card_of_Times_Func_Func: "|A \<times> B| <o |Func A (Func B (UNIV::bool set))|"
proof-  
  note card_of_Pow   
  also note card_of_Pow_Func 
  also note card_of_Func_Times  
  finally show ?thesis .
qed

(*
lemma card_of_Func_cong: "|A1| =o |A2| \<Longrightarrow> |B1| =o |B2| \<Longrightarrow> |Func A1 B1| =o |Func A2 B2|" 
*)

end