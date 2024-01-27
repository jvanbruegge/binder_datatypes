theory ILC2 
imports ILC "../Generic_Barendregt_Enhanced_Rule_Induction"
begin

(* INSTANTIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: ivar" 
apply standard
  apply (simp add: infinite_ivar)
  using regularCard_ivar . 

instance ivar :: infinite_regular ..

lemma small_dsset[simp,intro]: "small (dsset xs)"
by (simp add: card_dsset_ivar small_def)

lemma small_image_sset[simp,intro]: "inj_on f (dsset xs) \<Longrightarrow> small (f ` dsset xs)"
by (metis countable_card_ivar countable_card_le_natLeq dsset.rep_eq small_def sset_natLeq stream.set_map)



end 