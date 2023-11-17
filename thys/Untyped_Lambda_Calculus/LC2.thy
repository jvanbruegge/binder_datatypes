theory LC2 
imports LC "../Generic_Barendregt_Enhanced_Rule_Induction"
begin

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: var" 
apply standard
  apply (simp add: infinite_var)  
  using var_term_pre_class.regular by blast

end