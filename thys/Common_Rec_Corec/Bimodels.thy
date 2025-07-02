theory Bimodels
  imports Expressions
begin

consts \<phi> :: "('a::var,'a,'e,'e) G \<Rightarrow> bool"
axiomatization where \<phi>_Gmap: "\<And> u f g. \<phi> (Gmap f g u) \<longleftrightarrow> \<phi> u"
and \<phi>_Gren: "\<And> u \<sigma>. small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> \<phi> (Gren \<sigma> \<sigma> u) \<longleftrightarrow> \<phi> u"
(* this ensures \<phi> always covers base cases only  *)
and \<phi>_base: "\<And>u. \<phi> u \<Longrightarrow> GSupp1 u = {} \<and> GSupp2 u = {}"

lemma \<phi>_Gmap_eq: "\<phi> u \<Longrightarrow> Gmap f1 f2 u = Gmap g1 g2 u"
apply(rule Gmap_cong) using \<phi>_base by auto


type_synonym 'a E' = "'a E" 
(* Special iteration model, with syntactic domain; 
I keep E' as an abbreviation for E to avoid confusion: *)
locale Bimodel = 
fixes Ector0' :: "('a::var,'a,'a P\<Rightarrow>'a E','a P\<Rightarrow>'a E') G \<Rightarrow> 'a P\<Rightarrow>'a E'" 
and Ector1' :: "('a::var,'a,'a P\<Rightarrow>'a E','a P\<Rightarrow>'a E') G \<Rightarrow> 'a P\<Rightarrow>'a E'" 
(* Eperm and EVrs are the syntactic ones. Eperm and EVrs, 
so no need to assume nom for them since its known *)
(* 
and Eperm :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs :: "E' \<Rightarrow> var set"
assumes nom: "nom Eperm EVrs"
*)
assumes
    ctor0PermM: "\<And>u. \<phi> u \<Longrightarrow> ctorPermM Ector0' Eperm u" and 
    ctor1PermM: "\<And>u. \<not> \<phi> u \<Longrightarrow> ctorPermM Ector1' Eperm u"
and ctor0VarsM: "\<And>u. \<phi> u \<Longrightarrow> ctorVarsM Ector0' EVrs u" and 
    ctor1VarsM: "\<And>u. \<not> \<phi> u \<Longrightarrow> ctorVarsM Ector1' EVrs u"
(* above just standard model properties, but split in two; next some 
more specific requirements *)
assumes Ector_\<phi>_inj: "\<And>u1 u2::('a,'a,'a E, 'a E)G. \<phi> u1 \<Longrightarrow> Ector u1 = Ector u2 \<Longrightarrow> u1 = u2"
(* and Eperm_Eperm: "Eperm = Eperm"
and EVrs_EVrs: "EVrs = EVrs"
*)
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
(******)
and 
Ector_Ector1'_sync:  
"\<And>w u p g. GVrs2 w \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector w = Ector1' u p \<Longrightarrow> 
       Ector (Gmap g g w) = Ector1' (Gmap (\<lambda>pe. g o pe) (\<lambda>pe. g o pe) u) p"
and Ector1'_uniform:  
"\<And>u p. GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector1' u p = Ector1' (Gmap (\<lambda>pe p'. pe p) (\<lambda>pe p'. pe p) u) p" 
(* only depends on p *) 
begin

lemmas Ector1_Ector'_topFree' =  triv_Un4_remove[OF Ector1_Ector'_topFree]

lemma Ector_\<phi>: "Ector (u:: ('a, 'a, 'a E, 'a E) G) = Ector v \<Longrightarrow> \<phi> u \<longleftrightarrow> \<phi> v"
using Ector_\<phi>_inj by metis

lemma \<phi>_Some_Ector: "\<phi> (u:: ('a, 'a, 'a E, 'a E) G) \<Longrightarrow> (SOME ua. Ector ua = Ector u) = u"
by (metis (mono_tags, lifting) Ector_\<phi>_inj tfl_some) 

lemma \<phi>_Some_Ector': "\<phi> (SOME ua. Ector ua = Ector u) \<longleftrightarrow> \<phi> (u:: ('a, 'a, 'a E, 'a E) G)"
by (metis (mono_tags, lifting) Ector_\<phi>_inj tfl_some) 

(* *)

lemma Ector_Ector1'_Gmap: 
fixes w u :: "('a, 'a, 'a E, 'a E) G"   
assumes "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}"
and "Ector w = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
shows "Ector (Gmap (\<lambda>e. F e p) (\<lambda>e. F e p) w) =
       Ector1' (Gmap F F u) p"
proof-
  define F' where "F' \<equiv> ((\<lambda>pe::'a P\<Rightarrow>'a E. (\<lambda>e. F e p) o pe)) o (\<lambda>e p. e)"
  have F': "F' = (\<lambda>pe p'. pe p) o F" unfolding F'_def o_def fun_eq_iff by simp
  have 1: "Ector1' (Gmap F F u) p = Ector1' (Gmap F' F' u) p"
    unfolding F' Gmap_comp[symmetric]
    apply(rule Ector1'_uniform) unfolding GVrs2_Gmap using assms by auto
  show ?thesis unfolding 1 unfolding F'_def apply(subst Gmap_comp[symmetric])
    apply(rule Ector_Ector1'_sync) using assms unfolding GVrs2_Gmap by auto
qed

lemma Ector_Ector1'_Gmap_fst: 
assumes "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}"
and "Ector (Gmap fst fst w) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
and 00: "GSupp1 (Gmap snd snd w) \<union> GSupp2 (Gmap snd snd w) \<subseteq> {p}"
shows "Ector (Gmap (uncurry H) (uncurry H) w) = Ector1' (Gmap H H u) p"
proof-
  have 1: "Gmap (uncurry H) (uncurry H) w = Gmap (\<lambda>e. H e p) (\<lambda>e. H e p) (Gmap fst fst w)"
    unfolding Gmap_comp
    apply(rule Gmap_cong) using 00 unfolding GSupp1_Gmap GSupp2_Gmap uncurry_def by auto

  define H' where "H' \<equiv> \<lambda>e (p'::'a P). H e p"
  have H': "H' = (\<lambda>pe p'. pe p) o H" unfolding H'_def o_def fun_eq_iff by simp
  have 2: "Ector1' (Gmap H H u) p = Ector1' (Gmap H' H' u) p"
  unfolding H' Gmap_comp[symmetric]
  apply(rule Ector1'_uniform) using assms unfolding GVrs2_Gmap by auto
  have 11: "H' = (\<lambda>pe. (\<lambda>e. H e p) o pe) o (\<lambda>e (p::'a P). e)" 
    unfolding H'_def fun_eq_iff by auto

  show ?thesis unfolding 2 unfolding 11 unfolding 1 Gmap_comp[symmetric]
    apply(rule Ector_Ector1'_sync) using assms unfolding GVrs2_Gmap by auto
qed

end (* context Bimodels *)
 

end