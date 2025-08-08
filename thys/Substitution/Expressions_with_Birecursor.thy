theory Expressions_with_Birecursor
  imports Expressions_with_Subst
begin

(* The birecursor works for 
any polymorphic predicate base that satisfies 
base_Gmap, base_Gren and base_GSupp.
But here I define the spacific "base" 
using the substitution factory (\<eta>1 and \<eta>2)
*)

definition 
base :: "('a::var,'a,'e,'e) G \<Rightarrow> bool" 
where 
"base u \<equiv> \<exists>a. u = \<eta> a \<or> u = \<eta>' a"
lemma base_Gmap: "\<And> u f g. base (Gmap f g u) \<longleftrightarrow> base u"
and base_Gren: "\<And> (u::('a::var,'a,'e,'e) G) \<sigma>. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| 
   \<Longrightarrow> base (Gren \<sigma> \<sigma> u) \<longleftrightarrow> base u"
(* this ensures base always covers base cases only  *)
and base_GSupp: "\<And>u. base u \<Longrightarrow> GSupp1 u = {} \<and> GSupp2 u = {}"
apply-
  subgoal for u f g unfolding base_def 
    by (simp add: Gmap_eq_eta Gmap_eq_eta')
  subgoal for u \<sigma> unfolding base_def  
    by (metis Gren_eq_eta Gren_eq_eta' bij_implies_inject inv_simp2)
  subgoal for u unfolding base_def  
    by auto .

      
lemma base_Gmap_eq: "base u \<Longrightarrow> Gmap f1 f2 u = Gmap g1 g2 u"
by (metis G.Map_cong base_GSupp empty_iff)


definition lift :: "(('a::var \<Rightarrow> 'a) \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> 
 (('a::var \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>  
(('a \<Rightarrow> 'a) \<Rightarrow> ('p\<Rightarrow>'e) \<Rightarrow> ('p\<Rightarrow>'e))" where 
"lift Eperm Pperm \<sigma> pe p \<equiv> Eperm \<sigma> (pe (Pperm (inv \<sigma>) p))"

lemma triv_perm_lift: "(\<lambda>e p. e) \<circ> perm \<sigma> = lift perm pperm \<sigma> o (\<lambda>e p. e)"
  unfolding fun_eq_iff o_def lift_def by simp


locale Bimodel = 
  (* nominal-style binding-recursor assumptions, 
  including equivariance of Ector': *)
  NominalRel Pvalid Pperm "PVrs :: 'p \<Rightarrow> 'a :: var set" + Expression Eperm "EVrs :: 'e \<Rightarrow> 'a set" Ebd Ector
  for Pvalid Pperm PVrs Eperm EVrs Ebd Ector +
  fixes Ector' :: "('a::var, 'a, 'p \<Rightarrow> 'e, 'p \<Rightarrow> 'e) G \<Rightarrow> 'p \<Rightarrow> 'e"
  assumes 
  PVrs_small: "\<And>p. Pvalid p \<Longrightarrow> |PVrs p| <o |UNIV::'a set|"
  and Ector'_compat_Pvalid_step: "\<And>(u::('a, 'a, 'p\<Rightarrow>'e,'p\<Rightarrow>'e) G) f1 f2 g1 g2 p. 
   \<not> base u \<Longrightarrow> 
   (\<forall>pe \<in> GSupp1 u. \<forall>p. Pvalid p \<longrightarrow> f1 pe p = g1 pe p) \<Longrightarrow> 
   (\<forall>pe \<in> GSupp2 u. \<forall>p. Pvalid p \<longrightarrow> f2 pe p = g2 pe p) \<Longrightarrow>
   Pvalid p 
   \<Longrightarrow> 
   Ector' (Gmap f1 f2 u) p = Ector' (Gmap g1 g2 u) p"
  and Eperm_Ector': "\<And>\<sigma> p. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> Pvalid p \<Longrightarrow> 
    Eperm \<sigma> (Ector' u p) = 
    Ector' (Gren \<sigma> \<sigma> (Gmap (lift Eperm Pperm \<sigma>) (lift Eperm Pperm \<sigma>) u)) (Pperm \<sigma> p)"
  (* NB: The following is part of the usual binding-aware model 
    repertoire, just that its *formulation* of 
    this takes advanatage of the fact that the domain is 
    syntactic and the variable-operator is the syntactic one
   and uses a known property of Ector
  (perhaps we should revert back to the Ector-free formulation) *)
  and ctorVarsM_Ector': 
  "Pvalid p \<Longrightarrow>  
    EVrs (Ector' u p) \<subseteq> PVrs p \<union> 
     GVrs1 u \<union> 
     (\<Union> {EVrs (pe p) - GVrs2 u | pe . pe \<in> GSupp1 u}) \<union> 
     (\<Union> {EVrs (pe p) | pe . pe \<in> GSupp2 u})"
  (* birecursion-specific assumptions 
    (taking advantage of the domain-codomain coincidence): *)
  and Ector_base_inj: "\<And>u1 u2::('a,'a,'e,'e)G. base u1 \<Longrightarrow> Ector u1 = Ector u2 \<Longrightarrow> u1 = u2"
  and Ector_Ector'_inj_step: "\<And>u u' p. Pvalid p \<Longrightarrow> 
   \<not> base u \<Longrightarrow> \<not> base u' \<Longrightarrow> 
   GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u' \<inter> PVrs p = {} \<Longrightarrow>
   Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u') \<Longrightarrow> 
   Ector' u p = Ector' u' p"
  and Ector_Ector'_sync:  
    "\<And>w u p g. \<not> base u \<Longrightarrow> Pvalid p \<Longrightarrow> GVrs2 w \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       (\<forall>e \<in> GSupp1 w. EVrs (g e) \<subseteq> EVrs e \<union> PVrs p) \<Longrightarrow> 
       (\<forall>e \<in> GSupp1 w. \<forall>\<sigma>. |supp \<sigma>| <o |UNIV::'a set| \<and> bij \<sigma> \<and> imsupp \<sigma> \<inter> PVrs p = {} \<longrightarrow> 
                Eperm \<sigma> (g e) = g (Eperm \<sigma> e)) \<Longrightarrow> 
       Ector w = Ector' u p \<Longrightarrow> 
       Ector (Gmap g g w) = Ector' (Gmap (\<lambda>pe. g o pe) (\<lambda>pe. g o pe) u) p"
  and Ector'_uniform:  
    "\<And>u p. \<not> base u \<Longrightarrow> Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector' u p = Ector' (Gmap (\<lambda>pe p'. pe p) (\<lambda>pe p'. pe p) u) p" 
begin


lemmas ctor_compat_Pvalid_step_Ector' = Ector'_compat_Pvalid_step
lemmas ctorPermM_Ector' = Eperm_Ector'
thm Ector_base_inj
thm Ector_Ector'_inj_step 
thm Ector_Ector'_sync
thm Ector'_uniform 


lemma Ector'_compat_Pvalid: 
"\<And>(u::('a, 'a, 'p\<Rightarrow>'e,'p\<Rightarrow>'e) G) f1 f2 g1 g2 p. 
   (\<forall>pe \<in> GSupp1 u. \<forall>p. Pvalid p \<longrightarrow> f1 pe p = g1 pe p) \<Longrightarrow> 
   (\<forall>pe \<in> GSupp2 u. \<forall>p. Pvalid p \<longrightarrow> f2 pe p = g2 pe p) \<Longrightarrow>
   Pvalid p 
   \<Longrightarrow> 
   Ector' (Gmap f1 f2 u) p = Ector' (Gmap g1 g2 u) p"
using ctor_compat_Pvalid_step_Ector'
by (smt (verit, best) base_Gmap_eq)  


lemmas ctor_compat_Pvalid_Ector' = Ector'_compat_Pvalid 


lemma Ector_Ector'_EVrs: 
assumes (*b: "\<not> base u"
and *) p: "Pvalid p"  (*and v: "GVrs2 u \<inter> PVrs p = {}" *)
shows "EVrs (Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p) \<subseteq> EVrs (Ector u) \<union> PVrs p"
apply(rule subset_trans[OF ctorVarsM_Ector'[rule_format, OF p]])
unfolding GVrs1_Gmap GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap 
unfolding EVrs_Ector by auto 

lemma Ector_Ector'_EVrs_stepp: 
"\<comment> \<open> \<not> base u \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> \<close>
    Pvalid p \<Longrightarrow> GVrs2 uu \<inter> PVrs p = {} \<Longrightarrow>
    Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p = Ector uu \<Longrightarrow>
    EVrs (Ector uu) \<subseteq> EVrs (Ector u) \<union> PVrs p"
using Ector_Ector'_EVrs[of p u] 
by auto 

lemmas Ector_Ector'_EVrs_step' =  
triv_Un4_remove[OF Ector_Ector'_EVrs_stepp[unfolded EVrs_Ector]]

lemma Ector_base: "Ector (u:: ('a, 'a, 'e, 'e) G) = Ector v \<Longrightarrow> base u \<longleftrightarrow> base v"
using Ector_base_inj by metis

lemma base_Some_Ector: "base (u:: ('a, 'a, 'e, 'e) G) \<Longrightarrow> (SOME ua. Ector ua = Ector u) = u"
by (metis (mono_tags, lifting) Ector_base_inj tfl_some) 

lemma base_Some_Ector': "base (SOME ua. Ector ua = Ector u) \<longleftrightarrow> base (u:: ('a, 'a, 'e, 'e) G)"
by (metis (mono_tags, lifting) Ector_base_inj tfl_some) 

(* *)

lemma Ector_Ector'_Gmap: 
fixes w u :: "('a, 'a, 'e, 'e) G"   
assumes "\<not> base u" "Pvalid p" "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}"
and 0: "\<forall>e \<in> GSupp1 w. EVrs (F e p) \<subseteq> EVrs e \<union> PVrs p"
       "\<forall>e \<in> GSupp1 w. \<forall>\<sigma>. |supp \<sigma>| <o |UNIV::'a set| \<and> bij \<sigma> \<and> imsupp \<sigma> \<inter> PVrs p = {} \<longrightarrow> 
                Eperm \<sigma> (F e p) = F (Eperm \<sigma> e) p" 
and "Ector w = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
shows "Ector (Gmap (\<lambda>e. F e p) (\<lambda>e. F e p) w) =
       Ector' (Gmap F F u) p"
proof-
  define F' where "F' \<equiv> ((\<lambda>pe::'p\<Rightarrow>'e. (\<lambda>e. F e p) o pe)) o (\<lambda>e p. e)"
  have F': "F' = (\<lambda>pe p'. pe p) o F" unfolding F'_def o_def fun_eq_iff by simp
  have 1: "Ector' (Gmap F F u) p = Ector' (Gmap F' F' u) p"
    unfolding F' Gmap_comp[symmetric] 
    apply(rule Ector'_uniform) unfolding GVrs2_Gmap using assms  
    by (auto simp add: base_Gmap) 
  show ?thesis unfolding 1 unfolding F'_def apply(subst Gmap_comp[symmetric])
    apply(rule Ector_Ector'_sync) using assms 
    unfolding GVrs2_Gmap base_Gmap by auto
qed

(* NB: The following is only needed for uniqueness, so is not needed 
for the syntax with bindings development. *)
lemma Ector_Ector'_Gmap_fst: 
assumes "\<not> base u" "Pvalid p" "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}"
and 0: "\<forall>e \<in> fst ` GSupp1 w. EVrs (H e p) \<subseteq> EVrs e \<union> PVrs p"
       "\<forall>e \<in> fst ` GSupp1 w. \<forall>\<sigma>. |supp \<sigma>| <o |UNIV::'a set| \<and> bij \<sigma> \<and> imsupp \<sigma> \<inter> PVrs p = {} \<longrightarrow> 
                Eperm \<sigma> (H e p) = H (Eperm \<sigma> e) p"
and "Ector (Gmap fst fst w) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
and 00: "GSupp1 (Gmap snd snd w) \<union> GSupp2 (Gmap snd snd w) \<subseteq> {p}"
shows "Ector (Gmap (uncurry H) (uncurry H) w) = Ector' (Gmap H H u) p"
proof-
  have 1: "Gmap (uncurry H) (uncurry H) w = Gmap (\<lambda>e. H e p) (\<lambda>e. H e p) (Gmap fst fst w)"
    unfolding Gmap_comp
    apply(rule Gmap_cong) using 00 unfolding GSupp1_Gmap GSupp2_Gmap uncurry_def by auto

  define H' where "H' \<equiv> \<lambda>e (p'::'p). H e p"
  have H': "H' = (\<lambda>pe p'. pe p) o H" unfolding H'_def o_def fun_eq_iff by simp
  have 2: "Ector' (Gmap H H u) p = Ector' (Gmap H' H' u) p"
  unfolding H' Gmap_comp[symmetric]
  apply(rule Ector'_uniform) using assms unfolding GVrs2_Gmap by (auto simp add: base_Gmap)
  have 11: "H' = (\<lambda>pe. (\<lambda>e. H e p) o pe) o (\<lambda>e (p::'p). e)" 
    unfolding H'_def fun_eq_iff by auto

  show ?thesis unfolding 2 unfolding 11 unfolding 1 Gmap_comp[symmetric]
    apply(rule Ector_Ector'_sync) using assms unfolding GVrs2_Gmap base_Gmap GSupp1_Gmap GSupp2_Gmap
    by auto
qed

end (* context Bimodel *)



context Expression begin
(* Non-clashing: Barendregt's convention *)
definition 
"noclashE x \<equiv> GVrs2 x \<inter> (GVrs1 x \<union> (\<Union>e \<in> GSupp2 x. EVrs e)) = {}"

lemma Eperm_inv_iff: "|supp \<sigma>| <o |UNIV::'a set| \<Longrightarrow> bij \<sigma> \<Longrightarrow> Eperm (inv \<sigma>) e1 = e \<longleftrightarrow> e1 = Eperm \<sigma> e"
by (metis Eperm_comp' Eperm_id bij_betw_inv_into bij_inv_id1 id_apply inv_inv_eq supp_inv_bound)

end



locale Expression_with_Birecursor = Expression Eperm "EVrs :: 'e \<Rightarrow> 'a :: var set" Ebd Ector
  for Eperm EVrs Ebd Ector +
  fixes Pdummy :: 'p
  assumes rec: "\<forall>Pvalid Pperm (PVrs :: 'p \<Rightarrow> 'a set) Ector'.
    Bimodel Pvalid Pperm PVrs Eperm EVrs Ebd Ector Ector' \<longrightarrow> (\<exists>rec.
      ((\<forall>u p. Pvalid p \<and> 
              noclashE u \<and> GVrs2 u \<inter> PVrs p = {} 
              \<longrightarrow> 
              rec (Ector u) p = 
              Ector' (Gmap rec rec u) p) \<and>
       (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<longrightarrow> Pvalid p \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. Pvalid p \<longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)))"
begin

context fixes Pvalid Pperm and PVrs :: "'p \<Rightarrow> 'a set" and Ector'
  assumes BM: "Bimodel Pvalid Pperm PVrs Eperm EVrs Ebd Ector Ector'"
begin

definition rec where
  "rec = (SOME rec. ((\<forall>u p. Pvalid p \<and> noclashE u \<and> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> 
   rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and>
       (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<longrightarrow> Pvalid p \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. Pvalid p \<longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)))"

lemma rec_Ector: "Pvalid p \<Longrightarrow> noclashE u \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
  rec (Ector u) p = Ector' (Gmap rec rec u) p"
  using someI_ex[OF rec[rule_format, OF BM], THEN conjunct1] unfolding rec_def
  by blast

lemma rec_Eperm: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> Pvalid p \<Longrightarrow>  rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))"
  using someI_ex[OF rec[rule_format, OF BM], THEN conjunct2, THEN conjunct1] unfolding rec_def
  by blast

lemma rec_EVrs: "Pvalid p \<Longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e"
  using someI_ex[OF rec[rule_format, OF BM], THEN conjunct2, THEN conjunct2] unfolding rec_def
  by blast

end

end

context Expression begin

lemma permute_\<rho>:
  "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> = {} \<Longrightarrow> Eperm f (\<rho> a) = \<rho> (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho> a = Ector (\<eta> a)")
    apply (simp add: Gren_def eta_natural Eperm_Ector)
   apply simp
   apply (rule Eperm_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
     apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho> a = Ector (\<eta> a)")
   apply (simp add: Gren_def eta_natural Eperm_Ector)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done

lemma permute_\<rho>':
  "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>' = {} \<Longrightarrow> Eperm f (\<rho>' a) = \<rho>' (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho>' a = Ector (\<eta>' a)")
    apply (simp add: Gren_def eta'_natural Eperm_Ector)
   apply simp
   apply (rule Eperm_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho>' a = Ector (\<eta>' a)")
   apply (simp add: Gren_def eta'_natural Eperm_Ector)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done

definition "Esub_Pvalid \<equiv> \<lambda>(\<delta>, \<rho>, \<rho>'). |supp (\<delta> :: 'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<and>
  |SSupp (Ector o \<eta>) \<rho>| <o |UNIV::'a set| \<and>
  |SSupp (Ector o \<eta>') \<rho>'| <o |UNIV::'a set|"
definition "Esub_Pperm \<equiv> \<lambda>\<sigma> (\<delta>, \<rho>, \<rho>'). (\<sigma> o \<delta> o inv \<sigma>, Eperm \<sigma> o \<rho> o inv \<sigma>, Eperm \<sigma> o \<rho>' o inv \<sigma>)"
definition "Esub_PVrs \<equiv> \<lambda>(\<delta>, \<rho>, \<rho>'). imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'"
definition "Esub_Ector' \<equiv> \<lambda>u (\<delta>, \<rho>, \<rho>'). if \<exists>a. u = \<eta> a then \<rho> (SOME a. u = \<eta> a) else
   if \<exists>a. u = \<eta>' a then \<rho>' (SOME a. u = \<eta>' a) else Ector (Gsub \<delta> id (Gmap (\<lambda>rec. rec (\<delta>, \<rho>, \<rho>')) (\<lambda>rec. rec (\<delta>, \<rho>, \<rho>')) u))"
lemmas Esub_defs = Esub_Pvalid_def Esub_Pperm_def Esub_PVrs_def Esub_Ector'_def

thm G.Map_Sb[no_vars]

lemma Gmap_Gsub: 
"|supp (\<delta>1::'a1::var\<Rightarrow>'a1)| <o |UNIV::'a1 set| \<Longrightarrow> |supp (\<delta>2::'a2::var\<Rightarrow>'a2)| <o |UNIV::'a2 set| \<Longrightarrow> 
 Gmap (f1::'c1\<Rightarrow>'c1') (f2::'c2\<Rightarrow>'c2') (Gsub \<delta>1 \<delta>2 u) = Gsub \<delta>1 \<delta>2 (Gmap f1 f2 u)"
using G.Map_Sb[of \<delta>1 \<delta>2 f1 f2, unfolded o_def fun_eq_iff] by auto 

thm G.Sb_comp[no_vars]
thm G.Map_comp[no_vars]

(*
lemma Gmap_comp: "Gmap g1 g2 (Gmap f1 f2 u) = Gmap (g1 \<circ> f1) (g2 \<circ> f2) u"
apply(subst G.Map_comp[symmetric]) by auto
*)

lemma Gsub_comp: "|supp (f1::'a1 \<Rightarrow>'a1)| <o |UNIV::'a1 set| \<Longrightarrow> |supp (f2::'a2::var\<Rightarrow>'a2)| <o |UNIV::'a2 set| \<Longrightarrow>
       |supp (g1::'a1::var\<Rightarrow>'a1)| <o |UNIV::'a1 set| \<Longrightarrow> |supp (g2::'a2::var\<Rightarrow>'a2)| <o |UNIV::'a2 set| \<Longrightarrow> 
Gsub g1 g2 (Gsub f1 f2 u) = Gsub (g1 \<circ> f1) (g2 \<circ> f2) u"
apply(subst G.Sb_comp[symmetric]) by auto

lemma card_image_ordLess: "|A| <o r \<Longrightarrow> |h ` A| <o r"
by (metis card_of_image ordLeq_ordLess_trans)

lemma eq_Un3_image: "A1 = f ` B1 \<Longrightarrow> A2 = f ` B2 \<Longrightarrow> A3 = f ` B3 \<Longrightarrow> 
 A1 \<union> A2 \<union> A3 = f ` (B1 \<union> B2 \<union> B3)"
by auto

lemma in_Un2: "(a \<in> A1 \<Longrightarrow> f a \<in> B1) \<Longrightarrow> (a \<in> A2 \<Longrightarrow> f a \<in> B2) \<Longrightarrow> 
 a \<in> A1 \<union> A2 \<Longrightarrow> f a \<in> B1 \<union> B2"
by auto


lemma Eperm_eq_Ector_eta_imp: 
assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a::var set|"
and "Eperm \<sigma> e = Ector (\<eta> (\<sigma> a))"
shows "e = Ector (\<eta> a)"
proof-
  have "e = Eperm (inv \<sigma>) (Eperm \<sigma> e)" 
  apply(subst Eperm_comp'[symmetric])
  using assms by (auto simp: Eperm_id)
  also have "\<dots> = Eperm (inv \<sigma>) (Ector (\<eta> (\<sigma> a)))"
  using assms by simp
  also have "\<dots> = Ector (\<eta> a)" 
    by (simp add: Eperm_Ector Gren_def assms)
  finally show ?thesis .
qed

lemma Eperm_eq_Ector_eta'_imp: 
assumes "bij \<sigma>" "|supp \<sigma>| <o |UNIV::'a::var set|"
and "Eperm \<sigma> e = Ector (\<eta>' (\<sigma> a))"
shows "e = Ector (\<eta>' a)"
proof-
  have "e = Eperm (inv \<sigma>) (Eperm \<sigma> e)" 
  apply(subst Eperm_comp'[symmetric])
  using assms by (auto simp: Eperm_id)
  also have "\<dots> = Eperm (inv \<sigma>) (Ector (\<eta>' (\<sigma> a)))"
  using assms by simp
  also have "\<dots> = Ector (\<eta>' a)" 
    by (simp add: Eperm_Ector Gren_def assms)
  finally show ?thesis .
qed

lemma image_imsupp_IImsupp': 
assumes "|supp \<delta>| <o |UNIV::'a::var set|"
and "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV::'a set|" 
and "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV::'a set|"
and [simp]: "bij \<sigma>" "|supp \<sigma>| <o |UNIV:: 'a set|"
shows 
"imsupp (\<sigma> \<circ> \<delta> \<circ> inv \<sigma>) \<union> 
 IImsupp' (Ector \<circ> \<eta>) EVrs (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>) \<union>
 IImsupp' (Ector \<circ> \<eta>') EVrs (Eperm \<sigma> \<circ> \<rho>' \<circ> inv \<sigma>) =
 \<sigma> ` (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>')"
proof(rule eq_Un3_image)
  show "imsupp (\<sigma> \<circ> \<delta> \<circ> inv \<sigma>) = \<sigma> ` imsupp \<delta>"
  unfolding image_def apply safe
    subgoal for a
    apply(rule bexI[of _ "inv \<sigma> a"])
      subgoal by simp
      subgoal by (simp add: image_in_bij_eq imsupp_comp_image) .
    subgoal by (simp add: imsupp_comp_image) . 
  show "IImsupp' (Ector \<circ> \<eta>) EVrs (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>) = \<sigma> ` IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>"
  unfolding image_def apply safe
    subgoal for a
    apply(rule bexI[of _ "inv \<sigma> a"])
      subgoal by simp
      subgoal unfolding IImsupp'_def 
      apply(rule in_Un2[where f = "inv \<sigma>" 
       and ?A1.0 = "SSupp (Ector \<circ> \<eta>) (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>)"
       and ?A2.0 = "IImsupp (Ector \<circ> \<eta>) EVrs (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>)"])
        subgoal by (auto simp: SSupp_def Eperm_Ector Gren_def)
        subgoal apply (auto simp: EVrs_Eperm IImsupp_def SSupp_def Eperm_Ector Gren_def)
        by (metis Eperm_Ector Gmap_eta Gren_def Gsub_eta assms(4,5) inv_simp2)
        subgoal . . .
      subgoal unfolding IImsupp'_def  IImsupp_def SSupp_def  
      by simp (metis EVrs_Eperm Eperm_eq_Ector_eta_imp assms(4,5) bijection.intro
            bijection.inv_left image_eqI) . 
  show "IImsupp' (Ector \<circ> \<eta>') EVrs (Eperm \<sigma> \<circ> \<rho>' \<circ> inv \<sigma>) = \<sigma> ` IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'"
  unfolding image_def apply safe
    subgoal for a
    apply(rule bexI[of _ "inv \<sigma> a"])
      subgoal by simp
      subgoal unfolding IImsupp'_def 
      apply(rule in_Un2[where f = "inv \<sigma>" 
       and ?A1.0 = "SSupp (Ector \<circ> \<eta>') (Eperm \<sigma> \<circ> \<rho>' \<circ> inv \<sigma>)"
       and ?A2.0 = "IImsupp (Ector \<circ> \<eta>') EVrs (Eperm \<sigma> \<circ> \<rho>' \<circ> inv \<sigma>)"])
        subgoal by (auto simp: SSupp_def Eperm_Ector Gren_def)
        subgoal apply (auto simp: EVrs_Eperm IImsupp_def SSupp_def Eperm_Ector Gren_def)
        by (metis Eperm_Ector Gmap_eta' Gren_def Gsub_eta' assms(4,5) inv_simp2)
        subgoal . . .
      subgoal unfolding IImsupp'_def  IImsupp_def SSupp_def  
      by simp (metis EVrs_Eperm Eperm_eq_Ector_eta'_imp assms(4,5) bijection.intro
            bijection.inv_left image_eqI) . 
qed


term Ector

thm Ector_inject

term Gmap

lemma Gmap_o_aux:
"Gmap (\<lambda>pe. g (pe p)) (\<lambda>pe. g (pe p)) u = Gmap g g (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u)"
unfolding Gmap_comp o_def ..

lemma Ector_Gmap_eq_aux: 
assumes p: "|PVrs p| <o |UNIV::'a set|" and 
1: "GVrs2 w \<inter> PVrs p = {}" "GVrs2 u \<inter> PVrs p = {}" and 
0: "\<forall>e \<in> GSupp1 w. EVrs (g e) \<subseteq> EVrs e \<union> PVrs p"
   "\<forall>e \<in> GSupp1 w. \<forall>\<sigma>. |supp \<sigma>| <o |UNIV :: 'a set| \<and> bij \<sigma> \<and> imsupp \<sigma> \<inter> PVrs p = {} \<longrightarrow> 
                Eperm \<sigma> (g e) = g (Eperm \<sigma> e)"
and 2: "Ector w = Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u)" 
shows "Ector (Gmap g g w) = Ector (Gmap (\<lambda>pe. g (pe p)) (\<lambda>pe. g (pe p)) u)"
unfolding Gmap_o_aux
using assms 
apply(subst (asm) Ector_fresh_inject[where A = "PVrs p"])
apply (auto simp: GVrs2_Gmap)
subgoal for \<sigma> unfolding Ector_inject apply(rule exI[of _ \<sigma>])
unfolding id_on_def apply (auto simp: Gmap_Gren GVrs2_Gmap GSupp1_Gmap)
  subgoal by (metis IntI UnE empty_iff not_in_imsupp_same subsetD)
  subgoal  apply (auto simp: Gmap_comp Gmap_Gren')
  unfolding Gmap_comp[symmetric] apply(drule sym[of "Gmap _ _ _"])
  apply simp unfolding Gmap_comp
  apply(rule Gmap_cong)
  by (auto simp: GSupp1_Gren) . .

lemma Esub_PVrs_small:  
"|supp \<delta>| <o |UNIV::'a set| \<Longrightarrow>
 |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV::'a set| \<Longrightarrow>
 |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV::'a set| \<Longrightarrow>
 |Esub_PVrs (\<delta>, \<rho>, \<rho>')| <o |UNIV::'a set|"
unfolding Esub_PVrs_def 
by (simp add: imsupp_supp_bound infinite_class.Un_bound)


sublocale Esub: Bimodel where
  Pvalid = Esub_Pvalid and
  Pperm = Esub_Pperm and
  PVrs = Esub_PVrs and
  Eperm = Eperm and
  EVrs = EVrs and
  Ector = Ector and
  Ector' = Esub_Ector'
  apply standard
         apply (unfold Esub_defs)
  subgoal for \<sigma> p
    apply (cases p)
    apply (auto simp: supp_comp_bound)
    apply (meson SSupp_Eperm_comp(1) card_of_subset_bound infinite_class.Un_bound)
    apply (meson SSupp_Eperm_comp(2) card_of_subset_bound infinite_class.Un_bound)
    done
  subgoal for \<sigma> \<tau> p
    apply (cases p)
    apply (auto simp: fun_eq_iff o_inv_distrib Eperm_comp[THEN fun_cong, simplified])
    done
  subgoal for \<sigma> p
    apply (cases p)
    apply (auto simp: fun_eq_iff)
      apply (metis in_imsupp inv_simp1 inv_simp2 not_in_imsupp_same)
     apply (metis (no_types, lifting) Int_emptyI bij_id_imsupp inv_simp2 permute_\<rho>)
    apply (metis (no_types, lifting) Int_emptyI bij_id_imsupp inv_simp2 permute_\<rho>')
    done
  subgoal for \<sigma> p
    apply (cases p)
    using image_imsupp_IImsupp' by (simp add: fun_eq_iff) 
  subgoal for p apply(cases p) 
  apply simp apply(intro infinite_class.Un_bound)
    subgoal unfolding imsupp_def apply(intro infinite_class.Un_bound)
      subgoal by simp
      subgoal using card_image_ordLess by blast .
    subgoal unfolding IImsupp'_def apply(intro infinite_class.Un_bound)
      subgoal by simp
      subgoal unfolding IImsupp_def  
        by (meson EVrs_bound var_class.UN_bound) .
    subgoal unfolding IImsupp'_def apply(intro infinite_class.Un_bound)
      subgoal by simp
      subgoal unfolding IImsupp_def  
        by (meson EVrs_bound var_class.UN_bound) . .
  subgoal for u f1 f2 g1 g2 unfolding fun_eq_iff apply clarsimp apply safe
  apply (auto simp: eta_distinct eta_distinct' Gren_def eta_inject eta'_inject eta_natural eta'_natural
      Eperm_Ector G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
      G.Map_comp[THEN fun_cong, simplified] supp_comp_bound o_assoc[symmetric]
      Gmap_eq_eta eta_inject Gmap_eq_eta' eta'_inject
      dest: eta_inversion eta'_inversion)
   apply(subst Gmap_Gsub[symmetric])
     subgoal by simp subgoal by simp
     apply(subst Gmap_Gsub[symmetric])
       subgoal by simp subgoal by simp  
       apply(rule arg_cong[of _ _ Ector])
       apply(rule Gmap_cong)
       by (auto simp: G.Supp1_Sb G.Supp2_Sb) 
  subgoal for u \<sigma> p
    apply (cases p)
    apply (auto simp: eta_distinct eta_distinct' Gren_def eta_inject eta'_inject eta_natural eta'_natural
      Eperm_Ector G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
      G.Map_comp[THEN fun_cong, simplified] supp_comp_bound o_assoc[symmetric]
      dest: eta_inversion eta'_inversion)
    apply (intro arg_cong[where f=Ector] arg_cong[where f="Gsub _ _"] G.Map_cong)
     apply (auto simp: lift_def o_def Eperm_comp[THEN fun_cong, simplified]  id_def[symmetric] Eperm_id)
    done
  subgoal for u p
    apply (auto simp: EVrs_Ector G.Vrs_Sb G.Supp_Sb G.Vrs_Map G.Supp_Map eta_inject eta'_inject eta_distinct eta_distinct' split: if_splits)
    subgoal for \<delta> \<rho> \<rho>' x a
      apply (cases "\<rho> a = Ector (\<eta> a)")
       apply (auto simp: IImsupp'_def SSupp_def IImsupp_def EVrs_Ector Gmap_eq_eta)
       done
    subgoal for \<delta> \<rho> \<rho>' x a
      apply (cases "\<rho>' a = Ector (\<eta>' a)")
       apply (auto simp: IImsupp'_def SSupp_def IImsupp_def EVrs_Ector Gmap_eq_eta')
      done
    apply (metis in_imsupp not_in_imsupp_same)
    apply blast 
    by blast 
  (* *)
  subgoal for u1 u2 unfolding base_def 
  using Ector_inject by auto
  (* *)
  subgoal for u u' p
    apply (auto simp: eta_distinct eta_distinct' eta_inject eta'_inject Gren_def
      eta_natural[of id id, unfolded G.Sb_Inj, simplified]
      eta'_natural[of id id, unfolded G.Sb_Inj, simplified]
      eta_natural[of _ _ id id, unfolded G.Map_id, simplified]
      eta'_natural[of _ _ id id, unfolded G.Map_id, simplified]
      dest!: Ector_inject[THEN iffD1, of "\<eta> _"] Ector_inject[THEN iffD1, of "\<eta>' _"] Ector_inject[THEN iffD1, of _ "\<eta> _"] Ector_inject[THEN iffD1, of _ "\<eta>' _"]
        eta_inversion[of id id, unfolded G.Sb_Inj, simplified, OF sym]
        eta'_inversion[of id id, unfolded G.Sb_Inj, simplified, OF sym]
        eta_inversion[rotated -1] eta'_inversion[rotated -1]
        eta_inversion[of id id, unfolded G.Sb_Inj, simplified]
        eta'_inversion[of id id, unfolded G.Sb_Inj, simplified])
     apply assumption
      subgoal for \<delta> \<rho> \<rho>' apply (subst (asm) Ector_fresh_inject
      [where A = "\<Union> (EVrs ` (\<lambda>rec. rec (\<delta>, \<rho>, \<rho>')) ` (GSupp1 u)) - GVrs2 u - GVrs2 u'"])
      subgoal by(auto simp add: G.Vrs_Map2)  
      subgoal by (simp add: G.Vrs_Map2)
      subgoal apply(intro card_of_minus_bound UN_bound)
        subgoal apply(rule card_image_ordLess)
          by (rule ordLess_ordLeq_trans[OF G.Supp1_bd large'])
         subgoal using EVrs_bound . .
      subgoal  apply (subst Ector_fresh_inject[where A = "{}"])
        subgoal by auto  subgoal by auto
        subgoal using emp_bound by blast
        subgoal apply safe subgoal for \<sigma>
          apply(rule exI[of _ \<sigma>]) apply safe
            subgoal unfolding id_on_def   
            by (auto simp: G.Supp1_Sb G.Supp1_Map imsupp_def supp_def Int_def G.Vrs2_Sb) 
            subgoal apply(drule sym[where t = "Gmap (\<lambda>pe. pe (\<delta>, \<rho>, \<rho>')) (\<lambda>pe. pe (\<delta>, \<rho>, \<rho>')) u'"]) 
            by (auto simp: Gmap_Gsub Gren_def Gmap_comp Gsub_comp) . . . . .
  (* *)
  subgoal for w u p g  
    apply (cases p)
    apply (auto split: if_splits simp: eta_distinct eta_distinct'  eta_inject eta'_inject Gren_def
      eta_natural[of id id, unfolded G.Sb_Inj, simplified]
      eta'_natural[of id id, unfolded G.Sb_Inj, simplified]
      eta_natural[of _ _ id id, unfolded G.Map_id, simplified]
      eta'_natural[of _ _ id id, unfolded G.Map_id, simplified]
      G.Map_comp[THEN fun_cong, simplified] base_def
      dest!: Ector_inject[THEN iffD1, of "\<eta> _"] Ector_inject[THEN iffD1, of "\<eta>' _"] Ector_inject[THEN iffD1, of _ "\<eta> _"] Ector_inject[THEN iffD1, of _ "\<eta>' _"]
        eta_inversion[of id id, unfolded G.Sb_Inj, simplified, OF sym]
        eta'_inversion[of id id, unfolded G.Sb_Inj, simplified, OF sym]
        eta_inversion[rotated -1] eta'_inversion[rotated -1]
        eta_inversion[of id id, unfolded G.Sb_Inj, simplified]
        eta'_inversion[of id id, unfolded G.Sb_Inj, simplified])  
    subgoal for \<delta> \<rho> \<rho>' 
      apply (drule sym[of "Ector w"])
      apply(subst Gmap_comp[symmetric])
      apply(simp add: Gmap_Gsub[symmetric])
      apply(subst Gmap_comp) apply (drule sym[of _ "Ector w"])
      apply(subst o_def)+
      apply(rule Ector_Gmap_eq_aux[of Esub_PVrs "(\<delta>, \<rho>, \<rho>')" w _ g]) 
      using Esub_PVrs_small by (auto simp: Esub_PVrs_def GVrs2_Gsub) . 
  (* *)
  subgoal for u p
    apply (cases p)
    apply (auto split: if_splits simp: eta_distinct eta_distinct'  eta_inject eta'_inject Gren_def
      eta_natural[of id id, unfolded G.Sb_Inj, simplified]
      eta'_natural[of id id, unfolded G.Sb_Inj, simplified]
      eta_natural[of _ _ id id, unfolded G.Map_id, simplified]
      eta'_natural[of _ _ id id, unfolded G.Map_id, simplified]
      G.Map_comp[THEN fun_cong, simplified] comp_def
      dest!: Ector_inject[THEN iffD1, of "\<eta> _"] Ector_inject[THEN iffD1, of "\<eta>' _"] Ector_inject[THEN iffD1, of _ "\<eta> _"] Ector_inject[THEN iffD1, of _ "\<eta>' _"]
        eta_inversion[of id id, unfolded G.Sb_Inj, simplified, OF sym]
        eta'_inversion[of id id, unfolded G.Sb_Inj, simplified, OF sym]
        eta_inversion[rotated -1] eta'_inversion[rotated -1]
        eta_inversion[of id id, unfolded G.Sb_Inj, simplified]
        eta'_inversion[of id id, unfolded G.Sb_Inj, simplified])
    done
  done
end

(* Instance of the Expression_with_Birecursor locale by 
instantiating the parameter type 'p to to ('a \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'e)  \<times> ('a \<Rightarrow> 'e), 
so that parameters consist of triples (\<delta>,\<rho>,\<rho>') as required 
for the definition of substitution. *)

locale Expression_with_Birecursor_for_Subst = Expression_with_Birecursor where
  Eperm = Eperm and EVrs = "EVrs :: 'e \<Rightarrow> 'a :: var set" and Ebd = Ebd and Ector = Ector and
  Pdummy = "undefined :: ('a \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'e)  \<times> ('a \<Rightarrow> 'e)"
  for Eperm EVrs Ebd Ector
begin

definition "Esub \<delta> \<rho> \<rho>' e = rec Esub_Pvalid Esub_Pperm Esub_PVrs Esub_Ector' e (\<delta>, \<rho>, \<rho>')"

declare eta_inject[simp]
declare eta'_inject[simp]
declare eta_distinct[simp]

sublocale Esub: Expression_with_Subst Eperm EVrs Ebd Ector Esub
  apply standard
    subgoal apply (unfold Esub_def)
    apply (subst rec_Ector[OF Esub.Bimodel_axioms]) 
      subgoal unfolding Esub_Pvalid_def by auto
      subgoal unfolding noclashE_def by auto
      subgoal by simp
      subgoal unfolding Esub_Ector'_def by auto .
    subgoal apply (unfold Esub_def)
    apply (subst rec_Ector[OF Esub.Bimodel_axioms]) 
      subgoal unfolding Esub_Pvalid_def by auto
      subgoal unfolding noclashE_def by auto
      subgoal by simp
      subgoal unfolding Esub_Ector'_def using eta_distinct' by auto .
    subgoal for \<delta> \<rho> \<rho>' u apply (unfold Esub_def)
    apply (subst rec_Ector[OF Esub.Bimodel_axioms]) 
      subgoal unfolding Esub_Pvalid_def by auto
      subgoal unfolding noclashE_def by (auto simp: EVrs_Ector)
      subgoal unfolding Esub_PVrs_def by auto
      subgoal unfolding Esub_Ector'_def apply (auto simp: Gmap_comp)
        apply (smt (z3) Gsub_eta' eta'_inversion)
        apply (metis (no_types, lifting) Gsub_eta eta_inversion)
        apply(rule arg_cong[where f = Ector]) 
        apply(rule arg_cong[where f = "Gsub \<delta> id"])  
        apply(rule G.Map_cong) by auto .
      subgoal apply (unfold Esub_def) 
      apply(rule subset_trans[OF rec_EVrs[OF Esub.Bimodel_axioms]])
        subgoal unfolding Esub_Pvalid_def by auto
        subgoal unfolding Esub_PVrs_def by auto .

      subgoal for \<delta> \<rho> \<rho>' \<sigma> e apply (unfold Esub_def)  
      apply (subst rec_Eperm[OF Esub.Bimodel_axioms]; simp add: Esub_defs)
      apply (rule arg_cong[where f = "\<lambda>p. Eperm _ (rec _ _ _ _ _ p)"])
      apply (auto simp: fun_eq_iff)
        subgoal by (metis Int_Un_empty Int_emptyD bij_inv_rev imsupp_idle2 not_in_imsupp_same)
        subgoal by (metis (mono_tags, lifting) Int_Un_empty Int_Un_emptyI1 bij_betw_inv_into 
                   imsupp_inv inv_simp1 permute_\<rho> supp_inv_bound)
        subgoal by (smt (verit, best) Int_Un_empty Un_commute bij_betw_inv_into imsupp_inv inv_simp1 
                      permute_\<rho>' supp_inv_bound) . .
   
end (* context Expression_with_Birecursor_for_Subst *)

locale Expression_with_Birecursor_for_Subst_Strong = Expression_with_Birecursor_for_Subst + Expression_with_Surj_and_Coinduct
begin
sublocale Esub_Strong: Expression_with_Subst_Strong Eperm EVrs Ebd Ector Esub
  by standard
end

end

