theory LC2 
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction"
begin

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: var" 
apply standard by (simp add: infinite_var)   

end