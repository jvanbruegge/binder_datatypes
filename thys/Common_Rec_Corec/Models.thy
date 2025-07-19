theory Models 
  imports Expressions
begin


(* Iteration dynamic-Barendregt-enriched model (full-recursion not needed): *)
locale Model =
fixes Ector' :: "('a, 'a, 'a::var P\<Rightarrow>'E','a P\<Rightarrow>'E') G \<Rightarrow> 'a P \<Rightarrow> 'E'" 
and Eperm' :: "('a::var \<Rightarrow> 'a) \<Rightarrow> 'E' \<Rightarrow> 'E'" 
and EVrs' ::"'E' \<Rightarrow> 'a::var set" 
assumes nom: "nom (\<lambda>e. True) Eperm' EVrs'"
and ctorPermM: "\<And>u. ctorPermM Ector' Eperm' u"
and ctorVarsM: "\<And>u. ctorVarsM Ector' EVrs' u"
begin 


definition rec :: "'a E \<Rightarrow> 'a P \<Rightarrow> 'E'" where 
"rec = undefined"

lemma rec_Ector:
"Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> GVrs1 u = {} \<Longrightarrow>
 rec (Ector u) p = Ector' (Gmap rec rec u) p"
sorry

lemma rec_Eperm:
"Pvalid p \<Longrightarrow> small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow>  
 rec (Eperm \<sigma> e) p = Eperm' \<sigma> (rec e (Pperm (inv \<sigma>) p))"
sorry

lemma rec_EVrs: 
"Pvalid p \<Longrightarrow> EVrs' (rec e p) \<subseteq> PVrs p \<union> EVrs e"
sorry

lemma rec_unique:
assumes "\<And>u. Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> GVrs1 u = {} \<Longrightarrow>
  H (Ector u) p = Ector' (Gmap H H u) p"
shows "H = rec" 
sorry

end (* locale Model *)


end