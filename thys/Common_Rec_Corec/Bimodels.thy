theory Bimodels
  imports Expressions
begin


consts \<phi> :: "('e,'e) G \<Rightarrow> bool"
axiomatization where \<phi>_Gmap: "\<And> u f g. \<phi> (Gmap f g u) \<longleftrightarrow> \<phi> u"
axiomatization where \<phi>_Gren: "\<And> u \<sigma>. small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> \<phi> (Gren \<sigma> \<sigma> u) \<longleftrightarrow> \<phi> u"

type_synonym E' = E 
(* Special iteration model, with syntactic domain; 
I keep E' as an abbreviation for E to avoid confusion: *)
locale Bimodel = 
fixes Ector0' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'" 
and Ector1' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs' ::"E' \<Rightarrow> var set" 
assumes nom: "nom Eperm' EVrs'"
and ctor0PermM: "\<And>u. \<phi> u \<Longrightarrow> ctorPermM Ector0' Eperm' u" and 
    ctor1PermM: "\<And>u. \<not> \<phi> u \<Longrightarrow> ctorPermM Ector1' Eperm' u"
and ctor0VarsM: "\<And>u. \<phi> u \<Longrightarrow> ctorVarsM Ector0' EVrs' u" and 
    ctor1VarsM: "\<And>u. \<not> \<phi> u \<Longrightarrow> ctorVarsM Ector1' EVrs' u"
(* above just standard model properties, bu split in two; next some 
specific requirements *)
assumes Ector_\<phi>_inj: "\<And>u1 u2. \<phi> u1 \<Longrightarrow> \<comment> \<open>\<phi> u2 \<Longrightarrow>  \<close> Ector u1 = Ector u2 \<Longrightarrow> u1 = u2"
and Eperm'_Eperm: "Eperm' = Eperm"
and EVrs'_EVrs: "EVrs' = EVrs"
and Ector1_Ector'_inj: "\<And>u u1 p. \<not> \<phi> u \<Longrightarrow> \<not> \<phi> u1 \<Longrightarrow> 
   GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u1 \<inter> PVrs p = {} \<Longrightarrow> 
   Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u1) \<Longrightarrow> 
   Ector1' u p = Ector1' u1 p"
(* Ector1 is less injective that Ector outside \<phi>, and assuming freshness *)
and 
(* call the expression expression FreeVars u, and use it in the other axioms:  *)
Ector1_Ector'_topFree: "\<And>u uu p. \<not> \<phi> u \<Longrightarrow> 
    GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 uu \<inter> PVrs p = {} \<Longrightarrow>
    Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p = Ector uu \<Longrightarrow>
    GVrs1 uu \<union> \<Union> {EVrs e' |e'. e' \<in> GSupp1 uu} \<union> \<Union> {EVrs e' - GVrs2 uu |e'. e' \<in> GSupp1 uu} \<subseteq> 
    GVrs1 u \<union> \<Union> {EVrs e' |e'. e' \<in> GSupp1 u} \<union> \<Union> {EVrs e' - GVrs2 u |e'. e' \<in> GSupp1 u} \<union> PVrs p"
(* This can replace one axiom for ECtor1' (since it makes it redundant *)
begin

lemmas Ector1_Ector'_topFree' =  triv_Un4_remove[OF Ector1_Ector'_topFree]

lemma Ector_\<phi>: "Ector u = Ector v \<Longrightarrow> \<phi> u \<longleftrightarrow> \<phi> v"
using Ector_\<phi>_inj by metis

lemma \<phi>_Some_Ector: "\<phi> u \<Longrightarrow> (SOME ua. Ector ua = Ector u) = u"
by (metis (mono_tags, lifting) Ector_\<phi>_inj tfl_some) 

lemma \<phi>_Some_Ector': "\<phi> (SOME ua. Ector ua = Ector u) \<longleftrightarrow> \<phi> u"
by (metis (mono_tags, lifting) Ector_\<phi>_inj tfl_some) 


end (* context Bimodels *)
 

end