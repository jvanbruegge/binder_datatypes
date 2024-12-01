theory Sugar2
  imports "Binders.MRBNF_Recursor"
begin

declare [[mrbnf_internals]]
binder_datatype 'a FType
  = TyVar 'a
  | TyApp "'a FType" "'a FType"
  | TyAll a::'a t::"'a FType" binds a in t

thm FType.inject
thm FType.TT_inject0

definition swap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<leftrightarrow>" 400) where
  "swap a b \<equiv> \<lambda>x. if x = a then b else (if x = b then a else x)"

thm FType.TT_inject0[no_vars]

lemma TyAll_binject: "(TyAll a t = TyAll a' t') \<longleftrightarrow> ((a = a' \<or> a \<notin> FVars_FType t') \<and> permute_FType (a \<leftrightarrow> a') t = t')"
  sorry

lemma TT_inject1: "(FType_ctor x = FType_ctor y) =
(\<exists>f g. bij f \<and> |supp f| <o |UNIV| \<and> bij g \<and> |supp g| <o |UNIV| \<and>
  id_on (\<Union> (FVars_FType ` set3_FType_pre x) - set2_FType_pre x) f \<and>
  id_on (\<Union> (FVars_FType ` set3_FType_pre y) - set2_FType_pre y) g \<and>
  map_FType_pre id f (permute_FType f) id x = map_FType_pre id g (permute_FType g) id y)"
  sorry
(* Andrei *)
lemma TyAll_binject1: "(TyAll a t = TyAll a' t') \<longleftrightarrow> (\<exists>a''. a'' \<notin> (FVars_FType t - {a}) \<union> (FVars_FType t' - {a'})
  \<and> permute_FType (a \<leftrightarrow> a'') t = permute_FType (a' \<leftrightarrow> a'') t')"
  sorry

end