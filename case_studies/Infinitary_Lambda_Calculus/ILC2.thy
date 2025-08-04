theory ILC2 
imports ILC "Case_Studies.Generic_Barendregt_Enhanced_Rule_Induction"
begin

instance ivar :: uncountable_regular ..

lemma small_image_sset[simp,intro]: "inj_on (f :: 'a \<Rightarrow> 'a :: {uncountable_regular}) (dsset xs) \<Longrightarrow> small (f ` dsset xs)"
  by (auto simp: small_def dsset_card_ls simp flip: dsset_dsmap)

lemma snth_equiv[equiv]:
  fixes \<sigma>::"ivar \<Rightarrow> ivar"
  assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::ivar set|"
  shows "irrename \<sigma> (xs !! n) = smap (irrename \<sigma>) xs !! n"
  using assms by simp

end 
