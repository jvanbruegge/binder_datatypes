theory Expression_Like_Birecursor
  imports Expression_Like_Sub
begin

locale Bimodel = Nominal Pperm "PVrs :: 'p \<Rightarrow> 'a :: var set" + Expression Eperm "EVrs :: 'e \<Rightarrow> 'a set" Ector
  for Pperm PVrs Eperm EVrs Ector +
  fixes Ector' :: "('a::var, 'a, 'p \<Rightarrow> 'e, 'p \<Rightarrow> 'e) G \<Rightarrow> 'p \<Rightarrow> 'e"
  assumes TODO: "\<exists>P. P Ector'" (* TODO 1 here we need the assumptions on bimodels*)

(*
TODO the below Birecursor locale needs to be interpreted for both datatypes and codatatypes
in the respective theory Data and Codata using the recursor/corecursor
the existing interpretations in that theory that define substitution directly should be quite close
*)
locale Birecursor = Expression Eperm "EVrs :: 'e \<Rightarrow> 'a :: var set" Ector
  for Eperm EVrs Ector +
  fixes Pdummy :: 'p
  assumes rec: "\<forall>Pperm (PVrs :: 'p \<Rightarrow> 'a set) Ector'.
    Bimodel Pperm PVrs Eperm EVrs Ector Ector' \<longrightarrow> (\<exists>rec.
      ((\<forall>u p. GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and>
       (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)))"
begin

context fixes Pperm and PVrs :: "'p \<Rightarrow> 'a set" and Ector'
  assumes BM: "Bimodel Pperm PVrs Eperm EVrs Ector Ector'"
begin

definition rec where
  "rec = (SOME rec. ((\<forall>u p. GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and>
       (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)))"

lemma rec_Ector: "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> rec (Ector u) p = Ector' (Gmap rec rec u) p"
  using someI_ex[OF rec[rule_format, OF BM], THEN conjunct1] unfolding rec_def
  by blast

lemma rec_EPerm: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))"
  using someI_ex[OF rec[rule_format, OF BM], THEN conjunct2, THEN conjunct1] unfolding rec_def
  by blast

lemma rec_EVrs: "EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e"
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

definition "Esub_Pperm \<equiv> \<lambda>\<sigma> (\<delta>, \<rho>, \<rho>'). (\<sigma> o \<delta> o inv \<sigma>, Eperm \<sigma> o \<rho> o inv \<sigma>, Eperm \<sigma> o \<rho>' o inv \<sigma>)"
definition "Esub_PVrs \<equiv> \<lambda>(\<delta>, \<rho>, \<rho>'). imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'"
definition "Esub_Ector' \<equiv> \<lambda>u (\<delta>, \<rho>, \<rho>'). if \<exists>a. u = \<eta> a then \<rho> (SOME a. u = \<eta> a) else
   if \<exists>a. u = \<eta>' a then \<rho>' (SOME a. u = \<eta>' a) else Ector (Gsub \<delta> id (Gmap (\<lambda>rec. rec (\<delta>, \<rho>, \<rho>')) (\<lambda>rec. rec (\<delta>, \<rho>, \<rho>')) u))"
lemmas Esub_defs = Esub_Pperm_def Esub_PVrs_def Esub_Ector'_def

sublocale Esub: Bimodel where
  Pperm = Esub_Pperm and
  PVrs = Esub_PVrs and
  Eperm = Eperm and
  EVrs = EVrs and
  Ector = Ector and
  Ector' = Esub_Ector'
  apply standard
  apply (unfold Esub_defs)
  subgoal for \<sigma> \<tau>
    by (auto simp: fun_eq_iff o_inv_distrib Eperm_comp[THEN fun_cong, simplified])
  subgoal for \<sigma> p
    apply (cases p)
    apply (auto simp: fun_eq_iff)
      apply (metis in_imsupp inv_simp1 inv_simp2 not_in_imsupp_same)
     apply (metis (no_types, lifting) Int_emptyI bij_id_imsupp inv_simp2 permute_\<rho>)
    apply (metis (no_types, lifting) Int_emptyI bij_id_imsupp inv_simp2 permute_\<rho>')
    done
  subgoal
    (*trivial for now but needs a proper proof once the Bimodel properties are there*)
    sorry
  done

end

(*TODO after the Birecursor instance is there interpret this locale to get the Substitution and 
its properties for free*)
locale Birecursor_Sub = Birecursor where
  Eperm = Eperm and EVrs = "EVrs :: 'e \<Rightarrow> 'a :: var set" and Ector = Ector and
  Pdummy = "undefined :: ('a \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'e)  \<times> ('a \<Rightarrow> 'e)"
  for Eperm EVrs Ector
begin

definition "Esub \<delta> \<rho> \<rho>' e = rec Esub_Pperm Esub_PVrs Esub_Ector' e (\<delta>, \<rho>, \<rho>')"

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
  apply (rule arg_cong[where f = "\<lambda>p. Eperm _ (rec _ _ _ _ p)"])
  apply (auto simp: fun_eq_iff)
  apply (metis Int_Un_empty Int_emptyD bij_inv_rev imsupp_idle2 not_in_imsupp_same)
  apply (metis (mono_tags, lifting) Int_Un_empty Int_Un_emptyI1 bij_betw_inv_into imsupp_inv inv_simp1
      permute_\<rho> supp_inv_bound)
  apply (smt (verit, best) Int_Un_empty Un_commute bij_betw_inv_into imsupp_inv inv_simp1 permute_\<rho>'
      supp_inv_bound)
  done

end

end

