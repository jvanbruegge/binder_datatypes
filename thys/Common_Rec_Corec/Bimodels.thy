theory Bimodels
  imports Expressions
begin

consts base :: "('a::var,'a,'e,'e) G \<Rightarrow> bool"
axiomatization where base_Gmap: "\<And> u f g. base (Gmap f g u) \<longleftrightarrow> base u"
and base_Gren: "\<And> u \<sigma>. small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> base (Gren \<sigma> \<sigma> u) \<longleftrightarrow> base u"
(* this ensures base always covers base cases only  *)
and base_base: "\<And>u. base u \<Longrightarrow> GSupp1 u = {} \<and> GSupp2 u = {}"

lemma base_Gmap_eq: "base u \<Longrightarrow> Gmap f1 f2 u = Gmap g1 g2 u"
apply(rule Gmap_cong) using base_base by auto



type_synonym 'a E' = "'a E" 
(* Special iteration model, with syntactic domain; 
I keep E' as an abbreviation for E to avoid confusion: *)
locale Bimodel = 
fixes Ector' :: "('a::var,'a,'a P\<Rightarrow>'a E','a P\<Rightarrow>'a E') G \<Rightarrow> 'a P \<Rightarrow>'a E'"  
(* Eperm and EVrs are the syntactic ones. Eperm and EVrs, 
so no need to assume nom for them since its known *)
(* 
and Eperm :: "(var \<Rightarrow> var) \<Rightarrow> E' \<Rightarrow> E'" 
and EVrs :: "E' \<Rightarrow> var set"
assumes nom: "nom Eperm EVrs"
*)

assumes
    ctorPermM_Ector': "\<And>u. ctorPermM Ector' Eperm u"
and ctorVarsM_Ector': "\<And>u. ctorVarsM Ector' EVrs u"
(* above just standard model properties; 
next some more specific requirements *)
assumes Ector_base_inj: "\<And>u1 u2::('a,'a,'a E, 'a E)G. base u1 \<Longrightarrow> Ector u1 = Ector u2 \<Longrightarrow> u1 = u2"
and Ector_Ector'_inj_step: "\<And>u u1 p. \<not> base u \<Longrightarrow> \<not> base u1 \<Longrightarrow> 
   Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u1 \<inter> PVrs p = {} \<Longrightarrow> 
   Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u1) \<Longrightarrow> 
   Ector' u p = Ector' u1 p"
(* Ector1 is less injective than Ector outside base, and assuming freshness *)
and 
Ector_Ector'_EVrs_step: "\<And>u p.
    \<not> base u \<Longrightarrow> 
    Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {}
    \<Longrightarrow>
    EVrs (Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p) \<subseteq> EVrs (Ector u) \<union> PVrs p"
(* AtoD: what you assumed in Expression_like_Corecursor 
is not the above, but a converse of it modulo PVrs p!, namely: 
EVrs_Ector': "\<And>u p. \<not> base u \<Longrightarrow> 
  EVrs (Ector' u p) \<subseteq> PVrs p \<union> EVrs (Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u))"
*)
and
Ector_Ector'_sync:  
"\<And>w u p g. \<not> base u \<Longrightarrow> Pvalid p \<Longrightarrow> GVrs2 w \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector w = Ector' u p \<Longrightarrow> 
       Ector (Gmap g g w) = Ector' (Gmap (\<lambda>pe. g o pe) (\<lambda>pe. g o pe) u) p"
and Ector'_uniform:  
"\<And>u p. \<not> base u \<Longrightarrow> Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector' u p = Ector' (Gmap (\<lambda>pe p'. pe p) (\<lambda>pe p'. pe p) u) p" 
(* thus, uniforminty means that Ector' u p only depends on the values 
of the items in u on p.  *) 
begin

lemma Ector_Ector'_EVrs_stepp: 
"\<not> base u \<Longrightarrow> 
    Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 uu \<inter> PVrs p = {} \<Longrightarrow>
    Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p = Ector uu \<Longrightarrow>
    EVrs (Ector uu) \<subseteq> EVrs (Ector u) \<union> PVrs p"
using Ector_Ector'_EVrs_step[of u p] 
by auto 


lemmas Ector_Ector'_EVrs_step' =  
triv_Un4_remove[OF Ector_Ector'_EVrs_stepp[unfolded EVrs_Ector]]

lemma Ector_base: "Ector (u:: ('a, 'a, 'a E, 'a E) G) = Ector v \<Longrightarrow> base u \<longleftrightarrow> base v"
using Ector_base_inj by metis

lemma base_Some_Ector: "base (u:: ('a, 'a, 'a E, 'a E) G) \<Longrightarrow> (SOME ua. Ector ua = Ector u) = u"
by (metis (mono_tags, lifting) Ector_base_inj tfl_some) 

lemma base_Some_Ector': "base (SOME ua. Ector ua = Ector u) \<longleftrightarrow> base (u:: ('a, 'a, 'a E, 'a E) G)"
by (metis (mono_tags, lifting) Ector_base_inj tfl_some) 

(* *)

thm Gmap_comp

lemma Ector_Ector'_Gmap: 
fixes w u :: "('a, 'a, 'a E, 'a E) G"   
assumes "\<not> base u" "Pvalid p" "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}"
and "Ector w = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
shows "Ector (Gmap (\<lambda>e. F e p) (\<lambda>e. F e p) w) =
       Ector' (Gmap F F u) p"
proof-
  define F' where "F' \<equiv> ((\<lambda>pe::'a P\<Rightarrow>'a E. (\<lambda>e. F e p) o pe)) o (\<lambda>e p. e)"
  have F': "F' = (\<lambda>pe p'. pe p) o F" unfolding F'_def o_def fun_eq_iff by simp
  have 1: "Ector' (Gmap F F u) p = Ector' (Gmap F' F' u) p"
    unfolding F' Gmap_comp[symmetric]
    apply(rule Ector'_uniform) unfolding GVrs2_Gmap using assms  
    by (auto simp add: base_Gmap) 
  show ?thesis unfolding 1 unfolding F'_def apply(subst Gmap_comp[symmetric])
    apply(rule Ector_Ector'_sync) using assms unfolding GVrs2_Gmap base_Gmap by auto
qed

(* NB: The following is only needed for uniqueness, so is not needed 
for the syntax with bindings development. *)
lemma Ector_Ector'_Gmap_fst: 
assumes "\<not> base u" "Pvalid p" "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}"
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
  apply(rule Ector'_uniform) using assms unfolding GVrs2_Gmap by (auto simp add: base_Gmap)
  have 11: "H' = (\<lambda>pe. (\<lambda>e. H e p) o pe) o (\<lambda>e (p::'a P). e)" 
    unfolding H'_def fun_eq_iff by auto

  show ?thesis unfolding 2 unfolding 11 unfolding 1 Gmap_comp[symmetric]
    apply(rule Ector_Ector'_sync) using assms unfolding GVrs2_Gmap base_Gmap 
    by auto
qed


end (* context Bimodel *)
 

end