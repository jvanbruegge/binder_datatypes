theory Bimodels
  imports Expressions
begin

type_synonym 'a E' = "'a E" 
(* Special iteration model, with syntactic domain; 
I keep E' as an abbreviation for E to avoid confusion: *)
locale Bimodel = 
  fixes Ector' :: "('a::var,'a,'a P\<Rightarrow>'a E','a P\<Rightarrow>'a E') G \<Rightarrow> 'a P\<Rightarrow>'a E'" 
(* Eperm and EVrs are the syntactic ones. Eperm and EVrs, 
so no need to assume nom for them since its known *)
(* 
and Eperm :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs :: "E' \<Rightarrow> var set"
assumes nom: "nom Eperm EVrs"
*)
assumes
    ctor1PermM: "\<And>u. ctorPermM Ector' Eperm u"
and ctor1VarsM: "\<And>u. ctorVarsM Ector' EVrs u"
(* above just standard model properties, but split in two; 
next some more specific requirements *)
assumes Ector1_Ector'_inj: "\<And>u u1 p.
   GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u1 \<inter> PVrs p = {} \<Longrightarrow> 
   Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u1) \<Longrightarrow> 
   Ector' u p = Ector' u1 p"
(* Ector1 is less injective than Ector outside \<phi>, and assuming freshness *)
and 
(* call the expression FreeVars u, and use it in the other axioms:  *)
Ector1_Ector'_topFree: "\<And>u uu p.
    GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 uu \<inter> PVrs p = {} \<Longrightarrow>
    Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p = Ector uu \<Longrightarrow>
    EVrs (Ector uu)  \<subseteq> EVrs (Ector u) \<union> PVrs p"
(* This can replace one axiom for Ector' (since it makes it redundant *)
(******)
and 
Ector_Ector'_sync:  
"\<And>w u p g. GVrs2 w \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector w = Ector' u p \<Longrightarrow> 
       Ector (Gmap g g w) = Ector' (Gmap (\<lambda>pe. g o pe) (\<lambda>pe. g o pe) u) p"
and Ector'_uniform:  
"\<And>u p. GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector' u p = Ector' (Gmap (\<lambda>pe p'. pe p) (\<lambda>pe p'. pe p) u) p" 
(* only depends on p *) 
begin

lemmas Ector1_Ector'_topFree' =  triv_Un4_remove[OF Ector1_Ector'_topFree[unfolded EVrs_Ector]]

(* *)

lemma Ector_Ector'_Gmap: 
fixes w u :: "('a, 'a, 'a E, 'a E) G"   
assumes "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}"
and "Ector w = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
shows "Ector (Gmap (\<lambda>e. F e p) (\<lambda>e. F e p) w) =
       Ector' (Gmap F F u) p"
proof-
  define F' where "F' \<equiv> ((\<lambda>pe::'a P\<Rightarrow>'a E. (\<lambda>e. F e p) o pe)) o (\<lambda>e p. e)"
  have F': "F' = (\<lambda>pe p'. pe p) o F" unfolding F'_def o_def fun_eq_iff by simp
  have 1: "Ector' (Gmap F F u) p = Ector' (Gmap F' F' u) p"
    unfolding F' Gmap_comp[symmetric]
    apply(rule Ector'_uniform) unfolding GVrs2_Gmap using assms by auto
  show ?thesis unfolding 1 unfolding F'_def apply(subst Gmap_comp[symmetric])
    apply(rule Ector_Ector'_sync) using assms unfolding GVrs2_Gmap by auto
qed

lemma Ector_Ector'_Gmap_fst: 
assumes "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}"
and "Ector (Gmap fst fst w) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
and 00: "GSupp1 (Gmap snd snd w) \<union> GSupp2 (Gmap snd snd w) \<subseteq> {p}"
shows "Ector (Gmap (uncurry H) (uncurry H) w) = Ector' (Gmap H H u) p"
proof-
  have 1: "Gmap (uncurry H) (uncurry H) w = Gmap (\<lambda>e. H e p) (\<lambda>e. H e p) (Gmap fst fst w)"
    unfolding Gmap_comp
    apply(rule Gmap_cong) using 00 unfolding GSupp1_Gmap GSupp2_Gmap uncurry_def by auto

  define H' where "H' \<equiv> \<lambda>e (p'::'a P). H e p"
  have H': "H' = (\<lambda>pe p'. pe p) o H" unfolding H'_def o_def fun_eq_iff by simp
  have 2: "Ector' (Gmap H H u) p = Ector' (Gmap H' H' u) p"
  unfolding H' Gmap_comp[symmetric]
  apply(rule Ector'_uniform) using assms unfolding GVrs2_Gmap by auto
  have 11: "H' = (\<lambda>pe. (\<lambda>e. H e p) o pe) o (\<lambda>e (p::'a P). e)" 
    unfolding H'_def fun_eq_iff by auto

  show ?thesis unfolding 2 unfolding 11 unfolding 1 Gmap_comp[symmetric]
    apply(rule Ector_Ector'_sync) using assms unfolding GVrs2_Gmap by auto
qed

end (* context Bimodels *)
 

end