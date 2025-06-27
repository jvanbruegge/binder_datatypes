theory Models 
  imports Expressions
begin


(****)
(* Iteration dynamic-Barendregt-enriched model (full-recursion not needed): *)


(* Iteration model *)
locale Model =
fixes Ector' :: "(P\<Rightarrow>'E',P\<Rightarrow>'E') G \<Rightarrow> P \<Rightarrow> 'E'" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E'" 
and EVrs' ::"'E' \<Rightarrow> var set" 
assumes nom: "nom Eperm' EVrs'"
and ctorPermM: "\<And>u. ctorPermM Ector' Eperm' u"
and ctorVarsM: "\<And>u. ctorVarsM Ector' EVrs' u"
begin 


definition rec :: "E \<Rightarrow> P\<Rightarrow>'E'" where 
"rec = undefined"

lemma rec_Ector:
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow>  
 rec (Ector u) p = Ector' (Gmap rec rec u) p"
sorry

lemma rec_Eperm:
"small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow>  
 rec (Eperm \<sigma> e) p = Eperm' \<sigma> (rec e (Pperm (inv \<sigma>) p))"
sorry

lemma rec_EVrs: 
"EVrs' (rec e p) \<subseteq> PVrs p \<union> EVrs e"
sorry


lemma rec_unique:
assumes "\<And>u. GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> H (Ector u) p = Ector' (Gmap H H u) p"
shows "H = rec" 
sorry

end (* locale Model *)

(******)





 

end