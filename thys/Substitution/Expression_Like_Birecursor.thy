theory Expression_Like_Birecursor
  imports Expression_Like_Sub
begin

locale Bimodel = NominalRel Pvalid Pperm "PVrs :: 'p \<Rightarrow> 'a :: var set" + Expression Eperm "EVrs :: 'e \<Rightarrow> 'a set" Ector
  for Pvalid Pperm PVrs Eperm EVrs Ector +
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
TODO the below Birecursor locale needs to be interpreted for both datatypes and codatatypes
in the respective theory Data and Codata using the recursor/corecursor
the existing interpretations in that theory that define substitution directly should be quite close
*)
locale Birecursor = Expression Eperm "EVrs :: 'e \<Rightarrow> 'a :: var set" Ector
  for Eperm EVrs Ector +
  fixes Pdummy :: 'p
  assumes rec: "\<forall>Pvalid Pperm (PVrs :: 'p \<Rightarrow> 'a set) Ector'.
    Bimodel Pvalid Pperm PVrs Eperm EVrs Ector Ector' \<longrightarrow> (\<exists>rec.
      ((\<forall>u p. Pvalid p \<longrightarrow> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and>
       (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<longrightarrow> Pvalid p \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. Pvalid p \<longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)))"
begin

context fixes Pvalid Pperm and PVrs :: "'p \<Rightarrow> 'a set" and Ector'
  assumes BM: "Bimodel Pvalid Pperm PVrs Eperm EVrs Ector Ector'"
begin

definition rec where
  "rec = (SOME rec. ((\<forall>u p. Pvalid p \<longrightarrow> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and>
       (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<longrightarrow> Pvalid p \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. Pvalid p \<longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)))"

lemma rec_Ector: "Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> rec (Ector u) p = Ector' (Gmap rec rec u) p"
  using someI_ex[OF rec[rule_format, OF BM], THEN conjunct1] unfolding rec_def
  by blast

lemma rec_EPerm: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> Pvalid p \<Longrightarrow>  rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))"
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
    sorry
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

(*TODO after the Birecursor instance is there interpret this locale to get the Substitution and 
its properties for free*)
locale Birecursor_Sub = Birecursor where
  Eperm = Eperm and EVrs = "EVrs :: 'e \<Rightarrow> 'a :: var set" and Ector = Ector and
  Pdummy = "undefined :: ('a \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'e)  \<times> ('a \<Rightarrow> 'e)"
  for Eperm EVrs Ector
begin

definition "Esub \<delta> \<rho> \<rho>' e = rec Esub_Pvalid Esub_Pperm Esub_PVrs Esub_Ector' e (\<delta>, \<rho>, \<rho>')"

sublocale Esub: Substitution Eperm EVrs Ector Esub
  apply standard
      apply (unfold Esub_def)
      apply (subst rec_Ector[OF Esub.Bimodel_axioms]; auto simp add:
         eta_natural[of id id, unfolded G.Sb_Inj, simplified]
         eta_inject Esub_defs)
      apply (subst rec_Ector[OF Esub.Bimodel_axioms]; auto simp add:
         eta'_natural[of id id, unfolded G.Sb_Inj, simplified]
         eta_distinct' eta'_inject Esub_defs)
      apply (subst rec_Ector[OF Esub.Bimodel_axioms]; auto dest: eta_inversion[of id id, unfolded G.Sb_Inj, simplified] eta'_inversion[of id id, unfolded G.Sb_Inj, simplified] simp add:
         eta_distinct eta_inject eta_distinct' eta'_inject G.Map_comp[THEN fun_cong, simplified] comp_def Esub_defs)
   apply (rule order_trans[OF rec_EVrs[OF Esub.Bimodel_axioms]]; simp add: Esub_defs)
  apply (subst rec_EPerm[OF Esub.Bimodel_axioms]; simp add: Esub_defs)
  apply (rule arg_cong[where f = "\<lambda>p. Eperm _ (rec _ _ _ _ _ p)"])
  apply (auto simp: fun_eq_iff)
  apply (metis Int_Un_empty Int_emptyD bij_inv_rev imsupp_idle2 not_in_imsupp_same)
  apply (metis (mono_tags, lifting) Int_Un_empty Int_Un_emptyI1 bij_betw_inv_into imsupp_inv inv_simp1
      permute_\<rho> supp_inv_bound)
  apply (smt (verit, best) Int_Un_empty Un_commute bij_betw_inv_into imsupp_inv inv_simp1 permute_\<rho>'
      supp_inv_bound)
  done

end

end

