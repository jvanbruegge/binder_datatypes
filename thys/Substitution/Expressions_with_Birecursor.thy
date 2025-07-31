theory Expressions_with_Birecursor
  imports Expressions_with_Subst
begin


locale Bimodel = NominalRel Pvalid Pperm "PVrs :: 'p \<Rightarrow> 'a :: var set" + Expression Eperm "EVrs :: 'e \<Rightarrow> 'a set" Ebd Ector
  for Pvalid Pperm PVrs Eperm EVrs Ebd Ector +
  fixes Ector' :: "('a::var, 'a, 'p \<Rightarrow> 'e, 'p \<Rightarrow> 'e) G \<Rightarrow> 'p \<Rightarrow> 'e"
  assumes Eperm_Ector': "\<And>\<sigma> p. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> Pvalid p \<Longrightarrow>
    Eperm \<sigma> (Ector' u p) = 
    Ector' (Gren \<sigma> \<sigma> (Gmap (\<lambda>pe p. Eperm \<sigma> (pe (Pperm (inv \<sigma>) p))) (\<lambda>pe p. Eperm \<sigma> (pe (Pperm (inv \<sigma>) p))) u)) (Pperm \<sigma> p)"
  and EVrs_Ector': "\<And>u p. Pvalid p \<Longrightarrow> EVrs (Ector' u p) \<subseteq> PVrs p \<union> EVrs (Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u))"
  and Ector'_inj: "\<And>u u' p. Pvalid p \<Longrightarrow>
   GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u' \<inter> PVrs p = {} \<Longrightarrow>
   Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u') \<Longrightarrow> 
   Ector' u p = Ector' u' p"
  and Ector_Ector'_sync:  
    "\<And>w u p g. Pvalid p \<Longrightarrow> GVrs2 w \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector w = Ector' u p \<Longrightarrow> 
       Ector (Gmap g g w) = Ector' (Gmap (\<lambda>pe. g o pe) (\<lambda>pe. g o pe) u) p"
  and Ector'_uniform:  
    "\<And>u p. Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
       Ector' u p = Ector' (Gmap (\<lambda>pe p'. pe p) (\<lambda>pe p'. pe p) u) p" 
begin

end

(*
TODO the below Expression_with_Birecursor locale needs to be interpreted for both datatypes and codatatypes
in the respective theory Data and Codata using the recursor/corecursor
the existing interpretations in that theory that define substitution directly should be quite close
*)
(* 
definition restr2 :: "('a \<Rightarrow> 'p \<Rightarrow> 'b) \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> 'b" where 
"restr2 f P \<equiv> \<lambda>a p. if P p then f a p else undefined"
*)

context Expression begin
(* Non-clashing: Barendregt's convention *)
definition 
"noclashE x \<equiv> GVrs2 x \<inter> GVrs1 x = {}"
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
"|supp (g1::'a1::var\<Rightarrow>'a1)| <o |UNIV::'a1 set| \<Longrightarrow> |supp (g2::'a2::var\<Rightarrow>'a2)| <o |UNIV::'a2 set| \<Longrightarrow> 
 Gmap (f1::'c1\<Rightarrow>'c1') (f2::'c2\<Rightarrow>'c2') (Gsub g1 g2 u) = Gsub g1 g2 (Gmap f1 f2 u)"
using G.Map_Sb[of g1 g2 f1 f2, unfolded o_def fun_eq_iff] by auto 

thm G.Sb_comp[no_vars]
thm G.Map_comp[no_vars]

lemma Gmap_comp: "Gmap g1 g2 (Gmap f1 f2 u) = Gmap (g1 \<circ> f1) (g2 \<circ> f2) u"
apply(subst G.Map_comp[symmetric]) by auto

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

(*
lemma in_Un2': "(a \<in> A1 \<Longrightarrow> f a \<in> B2) \<Longrightarrow> (a \<in> A2 \<Longrightarrow> f a \<in> B1) \<Longrightarrow> 
 a \<in> A1 \<union> A2 \<Longrightarrow> f a \<in> B1 \<union> B2"
by auto
*)

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
  subgoal for u \<sigma> p
    apply (cases p)
    apply (auto simp: eta_distinct eta_distinct' Gren_def eta_inject eta'_inject eta_natural eta'_natural
      Eperm_Ector G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
      G.Map_comp[THEN fun_cong, simplified] supp_comp_bound o_assoc[symmetric]
      dest: eta_inversion eta'_inversion)
    apply (intro arg_cong[where f=Ector] arg_cong[where f="Gsub _ _"] G.Map_cong)
     apply (auto simp: o_def Eperm_comp[THEN fun_cong, simplified]  id_def[symmetric] Eperm_id)
    done
  subgoal for u p
    apply (auto simp: EVrs_Ector G.Vrs_Sb G.Supp_Sb G.Vrs_Map G.Supp_Map eta_inject eta'_inject eta_distinct eta_distinct' split: if_splits)
    subgoal for \<delta> \<rho> \<rho>' x a
      apply (cases "\<rho> a = Ector (\<eta> a)")
       apply (auto simp: IImsupp'_def SSupp_def IImsupp_def EVrs_Ector)
      done
    subgoal for \<delta> \<rho> \<rho>' x a
      apply (cases "\<rho>' a = Ector (\<eta>' a)")
       apply (auto simp: IImsupp'_def SSupp_def IImsupp_def EVrs_Ector)
      done
    apply (metis in_imsupp not_in_imsupp_same)
    apply (metis in_imsupp not_in_imsupp_same)
    done
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
         subgoal apply(rule card_image_ordLess) using G.Supp1_bd 
         (* AtoD: need assumption Gbd <o |UNIV::'a| *) sorry
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
      G.Map_comp[THEN fun_cong, simplified] comp_def
      dest!: Ector_inject[THEN iffD1, of "\<eta> _"] Ector_inject[THEN iffD1, of "\<eta>' _"] Ector_inject[THEN iffD1, of _ "\<eta> _"] Ector_inject[THEN iffD1, of _ "\<eta>' _"]
        eta_inversion[of id id, unfolded G.Sb_Inj, simplified, OF sym]
        eta'_inversion[of id id, unfolded G.Sb_Inj, simplified, OF sym]
        eta_inversion[rotated -1] eta'_inversion[rotated -1]
        eta_inversion[of id id, unfolded G.Sb_Inj, simplified]
        eta'_inversion[of id id, unfolded G.Sb_Inj, simplified])  
    sorry
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
      subgoal unfolding noclashE_def by auto
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

