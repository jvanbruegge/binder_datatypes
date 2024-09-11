theory BMV_Composition
  imports "Binders.MRBNF_Recursor"
begin

binder_datatype 'a type = Var 'a | App "'a type" "'a type list" | Forall x::'a t::"'a type" binds x in t

abbreviation "bd_type \<equiv> natLeq"

abbreviation "sb_type \<equiv> tvsubst_type"


(* Comp *)
type_synonym 'a T = "'a + 'a type"

end