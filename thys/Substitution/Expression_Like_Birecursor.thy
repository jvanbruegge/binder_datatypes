theory Expression_Like_Birecursor
  imports Expression_Like_Sub
begin

locale Bimodel = Nominal Pperm "PVrs :: 'p \<Rightarrow> 'a :: var set" + Expression Eperm "EVrs :: 'e \<Rightarrow> 'a set" Ector
  for Pperm PVrs Eperm EVrs Ector +
  fixes  is_base :: "('a::var, 'a, 'e, 'e) G \<Rightarrow> bool"
  and Ector_base :: "('a::var, 'a, 'e, 'e) G \<Rightarrow> 'p \<Rightarrow> 'e"
  and Ector_step :: "('a::var, 'a, 'p \<Rightarrow> 'e, 'p \<Rightarrow> 'e) G \<Rightarrow> 'p \<Rightarrow> 'e"
  assumes TODO: "\<exists>P. P is_base Ector_base Ector_step"

locale Birecursor = Bimodel Pperm "PVrs :: 'p \<Rightarrow> 'a set" Eperm "EVrs :: 'e \<Rightarrow> 'a :: var set" Ector is_base Ector_base Ector_step
  for Pperm PVrs Eperm EVrs Ector is_base Ector_base Ector_step +
  assumes rec: "\<exists>rec.
      ((\<forall>u p. is_base u \<longrightarrow> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector_base u p) \<and>
       (\<forall>u p. \<not> is_base u \<longrightarrow> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector_step (Gmap rec rec u) p) \<and>
       (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e))"
begin

definition rec where
  "rec = (SOME rec. ((\<forall>u p. is_base u \<longrightarrow> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector_base u p) \<and>
       (\<forall>u p. \<not> is_base u \<longrightarrow> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector_step (Gmap rec rec u) p) \<and>
       (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)))"

lemma rec_base: "is_base u \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> rec (Ector u) p = Ector_base u p"
  using someI_ex[OF rec, THEN conjunct1] unfolding rec_def
  by blast

lemma rec_Ector: "\<not> is_base u \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> rec (Ector u) p = Ector_step (Gmap rec rec u) p"
  using someI_ex[OF rec, THEN conjunct2, THEN conjunct1] unfolding rec_def
  by blast

lemma rec_EPerm: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))"
  using someI_ex[OF rec, THEN conjunct2, THEN conjunct2, THEN conjunct1] unfolding rec_def
  by blast

lemma rec_EVrs: "EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e"
  using someI_ex[OF rec, THEN conjunct2, THEN conjunct2, THEN conjunct2] unfolding rec_def
  by blast

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

sublocale Esub: Birecursor where
  Pperm = "\<lambda>\<sigma> (\<delta>, \<rho>, \<rho>'). (\<sigma> o \<delta> o inv \<sigma>, Eperm \<sigma> o \<rho> o inv \<sigma>, Eperm \<sigma> o \<rho>' o inv \<sigma>)" and
  PVrs = "\<lambda>(\<delta>, \<rho>, \<rho>'). imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'" and
  Eperm = Eperm and
  EVrs = EVrs and
  Ector = Ector and
  is_base = "\<lambda>u. \<exists>a. u = \<eta> a \<or> u = \<eta>' a" and
  Ector_base = "\<lambda>u (\<delta>, \<rho>, \<rho>'). if (\<exists>a. u = \<eta> a) then \<rho> (SOME a. u = \<eta> a) else \<rho>' (SOME a. u = \<eta>' a)" and
  Ector_step = "\<lambda>u (\<delta>, \<rho>, \<rho>'). Ector (Gsub \<delta> id (Gmap (\<lambda>rec. rec (\<delta>, \<rho>, \<rho>')) (\<lambda>rec. rec (\<delta>, \<rho>, \<rho>')) u))"
  apply standard
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
    sorry
  subgoal
    sorry
  done

definition "Esub \<delta> \<rho> \<rho>' e = Esub.rec e (\<delta>, \<rho>, \<rho>')"

interpretation Substitution Eperm EVrs Ector Esub
  apply standard
      apply (unfold Esub_def)
      apply (subst Esub.rec_base; auto simp add: eta_inject)
      apply (subst Esub.rec_base; auto simp add: eta_distinct' eta'_inject)
    apply (subst Esub.rec_Ector; auto simp add: G.Map_comp[THEN fun_cong, simplified] comp_def[of _ Esub.rec])
   apply (rule order_trans[OF Esub.rec_EVrs]; simp)
  apply (subst Esub.rec_EPerm; simp)
  apply (rule arg_cong[where f = "\<lambda>p. Eperm _ (Esub.rec _ p)"])
  apply (auto simp: fun_eq_iff)
  apply (metis Int_Un_empty Int_emptyD bij_inv_rev imsupp_idle2 not_in_imsupp_same)
  apply (metis (mono_tags, lifting) Int_Un_empty Int_Un_emptyI1 bij_betw_inv_into imsupp_inv inv_simp1
      permute_\<rho> supp_inv_bound)
  apply (smt (verit, best) Int_Un_empty Un_commute bij_betw_inv_into imsupp_inv inv_simp1 permute_\<rho>'
      supp_inv_bound)
  done

end

end
