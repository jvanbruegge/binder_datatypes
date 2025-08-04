(* This theory proves that a a binder-codatatype satisfies: 
Expression axiomatization, and, more strongly: 
-- the Expression_with_Surj_and_Coinduct axiomatization, 
and also 
-- the Expression_with_Birecursor axiomatization, 
and in particular to the Expression_with_Birecursor_for_Subst_Strong axioms.
*)



theory Codata
  imports Codata_Customization
begin


abbreviation "IMSUPP \<delta> \<rho> \<rho>' \<equiv> imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'"
abbreviation "small_support \<delta> \<rho> \<rho>' \<equiv>
  |supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set| \<and>
  |SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set| \<and>
  |SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"

lemma small_IMSUPP: "small_support (\<delta> :: 'a \<Rightarrow> 'a :: covar_G) \<rho> \<rho>' \<Longrightarrow> |IMSUPP \<delta> \<rho> \<rho>'| <o |UNIV :: 'a set|"
  by (simp add: G.Un_bound imsupp_supp_bound)

abbreviation "DTOR \<equiv> (\<lambda>\<delta> \<rho> \<rho>' e. {u. Ector u = e \<and> GVrs2 u \<inter> IMSUPP \<delta> \<rho> \<rho>' = {}})"

lemma IImsupp_comp_image:
  "bij (\<sigma> :: 'a \<Rightarrow> 'a::covar_G) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> IImsupp' (Ector \<circ> \<eta>) EVrs (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>) = \<sigma> ` IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>"
  "bij (\<sigma> :: 'a \<Rightarrow> 'a::covar_G) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> IImsupp' (Ector \<circ> \<eta>') EVrs (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>) = \<sigma> ` IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>"
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def image_iff)
         apply (metis (mono_tags, lifting) Eperm_Ector Gren_def Un_iff eta_natural inv_simp2 mem_Collect_eq)
        apply (smt (verit, del_insts) E.FVars_permute Eperm_Ector Gren_def UN_I Un_iff eta_natural image_in_bij_eq inv_simp2 mem_Collect_eq)
       apply (metis E.permute_bij Eperm_Ector Gren_def bij_not_equal_iff eta_natural)
      apply (metis E.FVars_permute E.permute_bij E.permute_inv_simp Eperm_Ector Gren_def eta_natural image_in_bij_eq inv_simp1)
     apply (metis (mono_tags, lifting) Eperm_Ector Gren_def Un_iff eta'_natural inv_simp2 mem_Collect_eq)
    apply (smt (verit, del_insts) E.FVars_permute Eperm_Ector Gren_def UN_I Un_iff eta'_natural image_in_bij_eq inv_simp2 mem_Collect_eq)
   apply (metis E.permute_bij Eperm_Ector Gren_def bij_not_equal_iff eta'_natural)
  apply (metis E.FVars_permute E.permute_bij E.permute_inv_simp Eperm_Ector Gren_def eta'_natural image_in_bij_eq inv_simp1)
  done

interpretation Esub: COREC
  "\<lambda>(\<delta>, \<rho>, \<rho>', e). (if \<exists>a. e = Ector (\<eta> a) then GMAP id id Inl Inl ` DTOR \<delta> \<rho> \<rho>' (\<rho> (SOME a. e = Ector (\<eta> a)))
     else if \<exists>a. e = Ector (\<eta>' a) then GMAP id id Inl Inl ` DTOR \<delta> \<rho> \<rho>' (\<rho>' (SOME a. e = Ector (\<eta>' a)))
     else GMAP \<delta> id (\<lambda>u. Inr (\<delta>, \<rho>, \<rho>', u)) (\<lambda>u. Inr (\<delta>, \<rho>, \<rho>', u)) ` DTOR \<delta> \<rho> \<rho>' e)"
  "\<lambda>\<sigma> (\<delta>, \<rho>, \<rho>', e). (\<sigma> o \<delta> o inv \<sigma>, Eperm \<sigma> o \<rho> o inv \<sigma>, Eperm \<sigma> o \<rho>' o inv \<sigma>, Eperm \<sigma> e)"
  "\<lambda>(\<delta>, \<rho>, \<rho>', e). EVrs e \<union> IMSUPP \<delta> \<rho> \<rho>'"
  "\<lambda>(\<delta>, \<rho>, \<rho>', e). small_support \<delta> \<rho> \<rho>'"
  apply standard
  subgoal for d
    apply (auto intro!: Un_bound simp: imsupp_supp_bound
        Ector_eta_inj Ector_eta_inj' eta_distinct' split: if_splits) []
      apply (metis E.TT_fresh_cases small_IMSUPP)
     apply (metis E.TT_fresh_cases small_IMSUPP)
    apply (metis E.TT_fresh_cases small_IMSUPP)
    done
  subgoal for X X' d
    apply (auto split: if_splits simp: map_sum_o_inj GMAP_def Gren_def 
        G.Map_Sb[THEN fun_cong, simplified]
        G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
        G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj
        Ector_eta_inj Ector_eta_inj' Ector_eta'_inj Ector_eta'_inj' eta_inject eta'_inject)
    subgoal for \<delta> \<rho> \<rho>' a u u'
      apply (subgoal_tac "Ector u' = Ector u")
       apply (subst (asm) Ector_fresh_inject[where A="IMSUPP \<delta> \<rho> \<rho>'"])
          apply blast
         apply blast
        apply (blast intro: small_IMSUPP)
       apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (rule exI[of _ \<sigma>])
        apply (auto simp: Gren_def 
            G.Map_Sb[THEN fun_cong, simplified]
            G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified])
        done
      apply simp
      done
    subgoal for \<delta> \<rho> \<rho>' a u u'
      apply (subgoal_tac "Ector u = Ector u'")
       apply (subst (asm) Ector_fresh_inject[where A="IMSUPP \<delta> \<rho> \<rho>'"])
          apply blast
         apply blast
        apply (blast intro: small_IMSUPP)
       apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (rule exI[of _ \<sigma>])
        apply (auto simp: Gren_def 
            G.Map_Sb[THEN fun_cong, simplified]
            G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified])
        done
      apply simp
      done
    subgoal for \<delta> \<rho> \<rho>' u u'
      apply (drule sym[of "Ector u'"])
      apply (subst (asm) Ector_fresh_inject[where A="IMSUPP \<delta> \<rho> \<rho>'"])
         apply blast
        apply blast
       apply (blast intro: small_IMSUPP)
      apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (rule exI[of _ \<sigma>])
        apply (auto simp: Gren_def comp_def
            permute_\<rho> permute_\<rho>' imsupp_commute[THEN fun_cong, simplified, of \<sigma> \<delta>] Int_Un_distrib
            G.Map_Sb[THEN fun_cong, simplified]
            G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified])
        done
      done
    subgoal for \<delta> \<rho> \<rho>' u u'
      apply (drule sym[of "Ector u'"])
      apply (subst (asm) Ector_fresh_inject[where A="IMSUPP \<delta> \<rho> \<rho>'"])
         apply blast
        apply blast
       apply (blast intro: small_IMSUPP)
      apply (erule exE conjE)+
      subgoal for \<sigma>
        apply (drule spec[of _ \<sigma>])
        apply (auto simp: Gren_def comp_def G.Vrs_Sb G.Vrs_Map
            permute_\<rho> permute_\<rho>' imsupp_commute[THEN fun_cong, simplified, of \<sigma> \<delta>] Int_Un_distrib
            G.Map_Sb[THEN fun_cong, simplified]
            G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified])
         apply (erule notE)
         apply (smt (verit, ccfv_threshold) Diff_iff Int_emptyD Un_iff id_on_def
            not_in_imsupp_same)
        apply (meson not_ordLeq_ordLess)
        done
      done
    done
  subgoal for d X
    apply (auto  simp: map_sum_o_inj GMAP_def Gren_def EVrs_Ector
        G.Map_Sb[THEN fun_cong, simplified]
        G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
        G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj
        Ector_eta_inj Ector_eta_inj' Ector_eta'_inj Ector_eta'_inj' eta_inject eta'_inject
        split: if_splits)
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho> b = Ector (\<eta> b)")
       apply (simp add: Ector_eta_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho>' b = Ector (\<eta>' b)")
       apply (simp add: Ector_eta'_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
         apply (metis in_imsupp not_in_imsupp_same)
        apply (metis in_imsupp not_in_imsupp_same)
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho> b = Ector (\<eta> b)")
       apply (simp add: Ector_eta_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho>' b = Ector (\<eta>' b)")
       apply (simp add: Ector_eta'_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho> b = Ector (\<eta> b)")
       apply (simp add: Ector_eta_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    subgoal for \<delta> \<rho> \<rho>' a b u
      apply (cases "\<rho>' b = Ector (\<eta>' b)")
       apply (simp add: Ector_eta'_inj)
      apply (drule sym[of "Ector u"])
      apply (subgoal_tac "a \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
       apply blast
      apply (subst IImsupp'_def)
      apply (auto simp: SSupp_def IImsupp_def EVrs_Ector intro!: exI[of _ b])
      done
    done
  subgoal for \<sigma> d
    apply (auto split: if_splits simp: map_sum_o_inj GMAP_def Gren_def Eperm_Ector
        G.Map_Sb[THEN fun_cong, simplified]
        G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
        G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj
        Ector_eta_inj Ector_eta_inj' Ector_eta'_inj Ector_eta'_inj' eta_inject eta'_inject
        eta_natural eta'_natural eta_distinct eta_distinct' image_image)
    subgoal for \<delta> \<rho> \<rho>' u a
      apply (drule arg_cong[where f="Eperm (inv \<sigma>)"])
      apply (auto simp: GMAP_def Gren_def Eperm_Ector Eperm_comp o_assoc[symmetric] Eperm_id
          G.Map_Sb[THEN fun_cong, simplified] Eperm_comp[THEN fun_cong, simplified]
          G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
          G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj Int_Un_distrib intro!:
          image_eqI[where x="GMAP (inv \<sigma>) (inv \<sigma>) (Eperm (inv \<sigma>)) (Eperm (inv \<sigma>)) u"])
        apply (metis Int_emptyD comp_assoc image_in_bij_eq imsupp_comp_image)
       apply (metis (no_types, lifting)  Int_emptyD comp_assoc image_in_bij_eq IImsupp_comp_image(1))
      apply (metis (no_types, lifting)  Int_emptyD comp_assoc image_in_bij_eq IImsupp_comp_image(2))
      done
    subgoal for \<delta> \<rho> \<rho>' e a u
      apply (drule arg_cong[where f="Eperm (inv \<sigma>)"])
      apply (auto simp: Gren_def Eperm_comp[THEN fun_cong, simplified] Eperm_id Eperm_Ector eta_natural)
      done
    subgoal for \<delta> \<rho> \<rho>' u a
      apply (drule arg_cong[where f="Eperm (inv \<sigma>)"])
      apply (auto simp: GMAP_def Gren_def Eperm_Ector Eperm_comp o_assoc[symmetric] Eperm_id
          G.Map_Sb[THEN fun_cong, simplified] Eperm_comp[THEN fun_cong, simplified]
          G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
          G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj Int_Un_distrib intro!:
          image_eqI[where x="GMAP (inv \<sigma>) (inv \<sigma>) (Eperm (inv \<sigma>)) (Eperm (inv \<sigma>)) u"])
        apply (metis Int_emptyD comp_assoc image_in_bij_eq imsupp_comp_image)
       apply (metis (no_types, lifting)  Int_emptyD comp_assoc image_in_bij_eq IImsupp_comp_image(1))
      apply (metis (no_types, lifting)  Int_emptyD comp_assoc image_in_bij_eq IImsupp_comp_image(2))
      done
    subgoal for \<delta> \<rho> \<rho>' e a u
      apply (drule arg_cong[where f="Eperm (inv \<sigma>)"])
      apply (auto simp: Gren_def Eperm_comp[THEN fun_cong, simplified] Eperm_id Eperm_Ector eta'_natural)
      done
    subgoal for \<delta> \<rho> \<rho>' e u
      apply (drule arg_cong[where f="Eperm (inv \<sigma>)"])
      apply (auto simp: GMAP_def Gren_def Eperm_Ector Eperm_comp o_assoc[symmetric] Eperm_id supp_comp_bound
          comp_def[of "map_sum _ _"] comp_def[of "\<lambda>x. Inr (_, _, _, Eperm \<sigma> x)"]
          G.Map_Sb[THEN fun_cong, simplified] Eperm_comp[THEN fun_cong, simplified]
          G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
          G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj Int_Un_distrib intro!:
          image_eqI[where x="GMAP (inv \<sigma>) (inv \<sigma>) (Eperm (inv \<sigma>)) (Eperm (inv \<sigma>)) u"])
        apply (metis Int_emptyD comp_assoc image_in_bij_eq imsupp_comp_image)
       apply (metis (no_types, lifting)  Int_emptyD comp_assoc image_in_bij_eq IImsupp_comp_image(1))
      apply (metis (no_types, lifting)  Int_emptyD comp_assoc image_in_bij_eq IImsupp_comp_image(2))
      done
    done
  subgoal
    by (auto simp: Eperm_comp[THEN fun_cong, simplified] fun_eq_iff o_inv_distrib)
  subgoal for d \<sigma>
    apply (auto intro!: Eperm_cong_id simp: fun_eq_iff)
      apply (metis in_imsupp inv_simp1 inv_simp2 not_in_imsupp_same)
     apply (metis (no_types, lifting) Int_emptyI bij_id_imsupp inv_simp2 permute_\<rho>)
    apply (metis (no_types, lifting) Int_emptyI bij_id_imsupp inv_simp2 permute_\<rho>')
    done
  subgoal for \<sigma> d
    apply (auto simp: supp_comp_bound Un_bound
        intro!: ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_Eperm_comp(1)]]
        ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_Eperm_comp(2)]])
    done
  subgoal for d u
    apply (auto simp: map_sum_o_inj GMAP_def Gren_def G.pred_set
        G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb G.Sb_Inj
        Ector_eta_inj Ector_eta_inj' Ector_eta'_inj Ector_eta'_inj' eta_inject eta'_inject
        split: if_splits)
    done
  done

definition "Esub \<delta> \<rho> \<rho>' e = Esub.COREC (\<delta>, \<rho>, \<rho>', e)"

lemma
  assumes
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  shows
    Esub_Ector\<eta>: "Esub \<delta> \<rho> \<rho>' (Ector (\<eta> a)) = \<rho> a"
    and Esub_Ector\<eta>': "Esub \<delta> \<rho> \<rho>' (Ector (\<eta>' a)) = \<rho>' a"
    and Esub_Ector:
    "GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
   GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  Esub \<delta> \<rho> \<rho>' (Ector u) = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u))"
    apply -
  unfolding Esub_def
  subgoal
    apply (insert Ector_fresh_surj'[of "IMSUPP \<delta> \<rho> \<rho>'" "\<rho> a"])
    apply (drule meta_mp)
     apply (simp add: assms small_IMSUPP)
    apply (erule exE)
    subgoal for u
      apply (subst Esub.COREC_DDTOR[of "GMAP id id Inl Inl u"])
        apply (auto simp: assms case_sum_o_inj Ector_eta_inj
          G.Map_Sb[THEN fun_cong, simplified]
          G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
          G.Sb_Inj G.Map_id GMAP_def Gren_def eta_inject)
      done
    done
  subgoal
    apply (insert Ector_fresh_surj'[of "IMSUPP \<delta> \<rho> \<rho>'" "\<rho>' a"])
    apply (drule meta_mp)
     apply (simp add: assms small_IMSUPP)
    apply (erule exE)
    subgoal for u
      apply (subst Esub.COREC_DDTOR[of "GMAP id id Inl Inl u"])
        apply (auto simp: assms case_sum_o_inj Ector_eta'_inj'
          G.Map_Sb[THEN fun_cong, simplified]
          G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
          G.Sb_Inj G.Map_id GMAP_def Gren_def eta_distinct eta'_inject)
      done
    done
  subgoal
    apply (subst Esub.COREC_DDTOR[of "GMAP \<delta> id (\<lambda>e. Inr (\<delta>, \<rho>, \<rho>', e)) (\<lambda>e. Inr (\<delta>, \<rho>, \<rho>', e)) u"])
    using assms
      apply (auto simp: case_sum_o_inj comp_def Ector_eta_inj Ector_eta'_inj
        G.Map_Sb[THEN fun_cong, simplified]
        G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
        G.Sb_Inj G.Map_id GMAP_def Gren_def eta_distinct eta'_inject)
    done
  done

lemma EVrs_Esub:
  assumes
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  shows "EVrs (Esub \<delta> \<rho> \<rho>' e)
    \<subseteq> EVrs e \<union> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>')"
  unfolding Esub_def
  apply (rule order_trans[OF Esub.COREC_FFVarsD])
   apply (auto simp: assms)
  done

lemma Eperm_Esub:
  assumes
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: covar_G)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::covar_G \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  shows "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
  imsupp f \<inter> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>') = {} \<Longrightarrow>
  Eperm f (Esub \<delta> \<rho> \<rho>' t) = Esub \<delta> \<rho> \<rho>' (Eperm f t)"
  using assms unfolding Esub_def
  apply (subst Esub.COREC_mmapD[symmetric])
     apply auto [3]
  apply (rule arg_cong[where f = Esub.COREC])
  apply (auto simp add: fun_eq_iff Int_Un_distrib permute_\<rho> permute_\<rho>' imsupp_commute)
  done



(**************) 
(* That binder codatatypes satisfy the 
strong expression axiomatization was already proved 
in theory Codata_Customization: *)

interpretation Expression_with_Surj_and_Coinduct Eperm EVrs "card_suc Gbd" Ector
using Expression_with_Surj_and_Coinduct_axioms .



(****************)
(* Starting to prove that binder datatypes validate 
the birecursion principle: *)


context 
fixes Pvalid :: "'p \<Rightarrow> bool" 
and Pperm :: "('a::covar_G \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p" 
and PVrs :: "'p \<Rightarrow> 'a set" and 
Ector' :: "('a, 'a, 'p \<Rightarrow> 'a E, 'p \<Rightarrow> 'a E) G \<Rightarrow> 'p \<Rightarrow> 'a E"
assumes bimodel: 
"Bimodel Pvalid Pperm PVrs Eperm EVrs (card_suc Gbd) Ector Ector'"
(*"Bimodel Pvalid Pperm PVrs Eperm EVrs Gbd Ector Ector'"  *)
begin 

(* Just getting all the Bomodel theorems *)
interpretation Bimodel Pvalid Pperm PVrs Eperm EVrs "card_suc Gbd" Ector Ector'
using bimodel .

(* *)

definition Evalid' :: "'a E\<times>'p \<Rightarrow> bool" where 
"Evalid' ep \<equiv> Pvalid (snd ep)"  

fun Edtor1' :: "'a E\<times>'p \<Rightarrow> (('a::covar_G,'a,'a E\<times>'p,'a E\<times>'p)G) set" where 
"Edtor1' (e,p) =
\<Union> { {u1 . Ector (Gmap fst fst u1) = Ector' u p \<and> 
          GSupp1 (Gmap snd snd u1) \<union>  GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
          GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {}} | 
       u . \<not> base u \<and> Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = e \<and> 
           GVrs2 u \<inter> PVrs p = {} \<and> GVrs2 u \<inter> GVrs1 u = {}}"
declare Edtor1'.simps[simp del]
lemmas Edtor1'_def = Edtor1'.simps

lemma in_Edtor1'_Ector_aux: 
assumes "\<not> base u" "Pvalid p" "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
shows "u1 \<in> Edtor1' (Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u),p) \<longleftrightarrow> 
  (Ector (Gmap fst fst u1) = Ector' u p \<and> 
   GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {})"
using assms unfolding Edtor1'_def by (auto intro: Ector_Ector'_inj_step)

lemma in_Edtor1'_Ector: 
assumes "\<not> base u" "Pvalid p" "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
shows "u1 \<in> Edtor1' (Ector u,p) \<longleftrightarrow> 
  (Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
   GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {})"
proof-
  define v where v: "v \<equiv> Gmap (\<lambda>e (p::'p). e) (\<lambda>e (p::'p). e) u"
  have u: "u = Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) v"
  unfolding v Gmap_comp o_def by simp
  show ?thesis using assms apply(subst u)  
  by (auto simp add: GVrs1_Gmap GVrs2_Gmap base_Gmap in_Edtor1'_Ector_aux v) 
qed

lemma Edtor1'_Ector: 
assumes "\<not> base u" "Pvalid p" "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}" 
shows "Edtor1' (Ector u,p) = 
  {u1 . Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
        GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
        GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {}}"
using in_Edtor1'_Ector[OF assms] by auto

fun Edtor' :: "'a E\<times>'p \<Rightarrow> 'a E + (('a::covar_G,'a,'a E\<times>'p,'a E\<times>'p)G)set" where 
"Edtor' (e,p) = (let u = (SOME u. e = Ector u) in 
  if base u then Inl (Ector' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p) else Inr (Edtor1' (e,p)))"
declare Edtor'.simps[simp del]
lemmas Edtor'_def = Edtor'.simps

lemma Edtor'_base: 
assumes "base u"
shows "Edtor' (Ector u, p) = Inl (Ector' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p)"
using assms unfolding Edtor'_def 
by (smt (verit, ccfv_threshold) Eps_cong base_Some_Ector)


lemma Edtor'_step: 
assumes "\<not> base u"
shows "Edtor' (Ector u, p) = Inr (Edtor1' (Ector u, p))"
using assms unfolding Edtor'_def 
by (smt (verit) Ector_base tfl_some) 

lemma Edtor'_Inl_base: "Edtor' (Ector u, p) = Inl U \<Longrightarrow> base u"
  using Edtor'_step by force 

lemma Edtor'_Inr_step: "Edtor' (Ector u, p) = Inr U \<Longrightarrow> \<not> base u"
  using Edtor'_base by force

find_theorems Ector name: surj


(* *)
lemma Edtor1'_NE: 
assumes base: "\<not> base u" and p: "Pvalid p"
shows "Edtor1' (Ector u, p) \<noteq> {}" using in_Edtor1'_Ector
proof-
  obtain u0 where u0u: "Ector u0 = Ector u" 
  and g: "GVrs2 u0 \<inter> PVrs p = {}" "GVrs2 u0 \<inter> GVrs1 u0 = {}" 
  using Ector_fresh_surj'[OF PVrs_small, OF p] by metis
  hence base: "\<not> base u0" using base using Ector_base by blast
  obtain uu1 where "Ector uu1 = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u0) p" 
  "GVrs2 uu1 \<inter> PVrs p = {}" "GVrs2 uu1 \<inter> GVrs1 uu1 = {}"
  using Ector_fresh_surj'[OF PVrs_small, OF p] by metis
  then have "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) uu1 \<in> Edtor1' (Ector u, p)" 
  unfolding u0u[symmetric] apply(subst in_Edtor1'_Ector[OF base p g]) apply safe
    subgoal unfolding Gmap_comp o_def by simp
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal unfolding GVrs2_Gmap by auto 
    subgoal unfolding GVrs1_Gmap GVrs2_Gmap by auto .
  thus ?thesis by auto
qed


lemma Udtor_ne: "Evalid' d \<Longrightarrow> Edtor' d = Inr X \<Longrightarrow> X \<noteq> {}"
apply (cases d) apply safe 
  subgoal for e p apply(rule Ector_exhaust'[of e]) apply simp
  subgoal for u apply(cases "base u")
    subgoal unfolding Edtor'_base by simp
    subgoal unfolding Edtor'_step Evalid'_def using Edtor1'_NE by simp . . .

fun EVrs'' where "EVrs'' (e,p) = EVrs e \<union> PVrs p"
declare EVrs''.simps[simp del]
lemmas EVrs''_def = EVrs''.simps

fun Eperm'' where "Eperm'' \<sigma> (e,p) = (Eperm \<sigma> e, Pperm \<sigma> p)"
declare Eperm''.simps[simp del]
lemmas Eperm''_def = Eperm''.simps

lemma fst_EPerm'[simp]: "fst \<circ> Eperm'' \<sigma> = Eperm \<sigma> o fst"
unfolding fun_eq_iff by (simp add: Eperm''_def)

lemma snd_EPerm'[simp]: "snd \<circ> Eperm'' \<sigma> = Pperm \<sigma> o snd"
unfolding fun_eq_iff by (simp add: Eperm''_def)

lemma Eperm''_id[simp]: "Pvalid (snd pe) \<Longrightarrow> Eperm'' id pe = pe"
  using Eperm''_def  
  by (metis Eperm_id Pperm_id id_apply snd_conv surj_pair)   

abbreviation small :: "('a::covar_G \<Rightarrow>'a) \<Rightarrow> bool"  
where "small \<sigma> \<equiv> |supp \<sigma>| <o |UNIV::'a set|"

lemma Eperm''_o: 
"Pvalid (snd ep) \<Longrightarrow> small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
Eperm'' (\<sigma>1 \<circ> \<sigma>2) ep = Eperm'' \<sigma>1 (Eperm'' \<sigma>2 ep)"
apply(cases ep) 
by (simp add: Eperm''_def Eperm_comp Pperm_comp Eperm_comp') 

lemma Eperm''_comp: 
"Pvalid p \<Longrightarrow> small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
 Eperm'' \<sigma>1 (Eperm'' \<sigma>2 (e,p)) = Eperm'' (\<sigma>1 \<circ> \<sigma>2) (e,p)"
by (simp add: Eperm''_def Eperm_comp Pperm_comp Eperm_comp') 

lemma Eperm''_cong:
"Pvalid p \<Longrightarrow> small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow>
 small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> \<forall>a\<in>EVrs'' (e,p). \<sigma>1 a = \<sigma>2 a \<Longrightarrow> Eperm'' \<sigma>1 (e,p) = Eperm'' \<sigma>2 (e,p)"
unfolding Eperm''_def EVrs''_def    
by (metis Eperm_cong Pperm_cong UnCI)    

lemma EVrs_Un_PVrs_small:
"Pvalid p \<Longrightarrow> |EVrs e \<union> PVrs p| <o |UNIV::'a::covar_G set|"
by (simp add: G.Un_bound PVrs_small)

lemma nomC: "NominalRel Evalid' Eperm'' EVrs''"
using NominalRel_axioms unfolding NominalRel_def 
apply safe
unfolding Evalid'_def Eperm''_def 
unfolding NominalRel_def    
by (auto simp add: EVrs''_def Eperm_comp' Pperm_comp Eperm_cong_id 
   Pperm_cong_id EVrs_Eperm PVrs_Pperm EVrs_Un_PVrs_small) 

(*
lemma Pvalid_Pperm[simp]: "Pvalid p \<Longrightarrow> small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> Pvalid (Pperm \<sigma> p)"
using nomP unfolding nom_def by blast
*)

lemmas PVrs_small
lemma small_PVrs_im: "small \<sigma> \<Longrightarrow> Pvalid p \<Longrightarrow> |PVrs p \<union> inv \<sigma> ` PVrs p| <o |UNIV::'a::covar_G set|"
using PVrs_small card_image_ordLess infinite_class.Un_bound by blast

(* "lemma dtorPermC: dtorPermC Evalid' Edtor' Eperm''" *)
lemma dtorPermC_Inl: 
"bij \<sigma> \<Longrightarrow> small \<sigma> \<Longrightarrow> Evalid' ep \<Longrightarrow> Edtor' ep = Inl e1 \<Longrightarrow> Edtor' (Eperm'' \<sigma> ep) = Inl (Eperm \<sigma> e1)" 
apply (cases ep) apply clarify subgoal for e p
unfolding Eperm''_def Evalid'_def 
  apply(rule Ector_exhaust_fresh[OF small_PVrs_im, of \<sigma> p e], simp_all)
  unfolding A_Int_Un_emp apply(erule conjE) apply simp
  subgoal for u apply(cases "base u")
    subgoal unfolding Edtor'_base    
    unfolding Eperm_Ector apply(subst Edtor'_base)
      subgoal using base_Gmap base_Gren by metis
      subgoal apply auto 
      apply(subst ctorPermM_Ector')
        subgoal by simp  subgoal by simp subgoal by simp
        subgoal unfolding Gmap_comp Gmap_Gren'
         unfolding lift_def o_def .. . .
     subgoal using Edtor'_step by auto . . .

lemma triv_Eperm_lift: "(\<lambda>e p. e) \<circ> Eperm \<sigma> = lift Eperm Pperm \<sigma> o (\<lambda>e p. e)"
  unfolding fun_eq_iff o_def lift_def by simp

lemma Eperm_inv_iff: "small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> Eperm (inv \<sigma>) e1 = e \<longleftrightarrow> e1 = Eperm \<sigma> e"
by (metis E.permute_bij E.permute_inv_simp inv_simp1 inv_simp2)

lemma dtorPermC_Inr: 
"bij \<sigma> \<Longrightarrow> small \<sigma> \<Longrightarrow> Evalid' ep \<Longrightarrow> Edtor' ep = Inr U 
 \<Longrightarrow> \<exists>U'. Edtor' (Eperm'' \<sigma> ep) = Inr U' \<and> 
          U' \<subseteq> Gren \<sigma> \<sigma> ` (Gmap (Eperm'' \<sigma>) (Eperm'' \<sigma>) ` U)" 
apply (cases ep) apply clarify subgoal for e p
unfolding Eperm''_def Evalid'_def 
  apply(rule Ector_exhaust_fresh[OF small_PVrs_im, of \<sigma> p e], simp_all)
  unfolding A_Int_Un_emp apply(erule conjE) apply simp
  subgoal for u apply(cases "base u")
    subgoal by (simp add: Edtor'_Inr_step)
    subgoal 
     apply(subgoal_tac "\<sigma> ` GVrs2 u \<inter> PVrs p = {}") 
     prefer 2 subgoal unfolding bij_inv_Un_triv by auto
     unfolding Edtor'_step apply safe 
     unfolding Eperm_Ector apply(subst Edtor'_step)
      subgoal using base_Gmap base_Gren by metis
      subgoal apply simp  
      apply(subst Edtor1'_Ector)
        subgoal using base_Gmap base_Gren by metis
        subgoal using Pperm_Pvalid by presburger
        subgoal unfolding GVrs2_Gmap GVrs2_Gren PVrs_Pperm  
          by (metis bij_is_inj image_Int image_empty)
        subgoal unfolding GVrs2_Gmap GVrs2_Gren GVrs1_Gmap GVrs1_Gren PVrs_Pperm  
        by (simp add: image_Int_empty) 
        subgoal unfolding image_def apply auto apply(subst Edtor1'_Ector)
        apply auto subgoal for u0
        apply(rule exI[of _ "Gren (inv \<sigma>) (inv \<sigma>) u0"]) apply safe
          prefer 2 subgoal apply(subst Gren_comp'[symmetric]) by auto 
          subgoal 
          apply(rule exI[of _ "Gren (inv \<sigma>) (inv \<sigma>) (Gmap (Eperm'' (inv \<sigma>)) (Eperm'' (inv \<sigma>)) u0)"])
          apply safe
            subgoal unfolding Gmap_comp Gmap_Gren'[symmetric] apply(subst Gmap_Gren'[symmetric])
              subgoal by auto 
              subgoal unfolding Gmap_comp apply simp 
              unfolding Gmap_o apply(subst o_def)
              apply(subst Eperm_Ector[symmetric])
                subgoal by auto
                subgoal by auto
                subgoal 
                unfolding Gmap_o[symmetric] 
                unfolding triv_Eperm_lift 
                unfolding Gmap_o
                unfolding o_def
                apply(subst (asm) ctorPermM_Ector'[symmetric]) 
                  subgoal by simp subgoal by simp subgoal by simp
                  subgoal apply(subst Eperm_inv_iff) by auto . . .
              subgoal for e' unfolding GSupp1_Gmap apply auto subgoal for b apply(subst (asm) GSupp1_Gren)
                subgoal by auto 
                subgoal unfolding GSupp1_Gmap apply(auto simp: Eperm''_def) subgoal for ee pp 
                apply(subgoal_tac "pp = Pperm \<sigma> p")
                  subgoal apply simp apply(subst Pperm_comp) by auto
                  subgoal by auto . . . .
              subgoal for pp unfolding GSupp2_Gmap apply auto apply(subst (asm) GSupp2_Gren)
                subgoal by auto 
                subgoal for ee unfolding GSupp2_Gmap apply(auto simp: Eperm''_def) subgoal for e' p'
                apply(subgoal_tac "p' = Pperm \<sigma> p")
                  subgoal apply simp apply(subst Pperm_comp) by auto
                  subgoal by auto . . . 
              subgoal for a apply(subst (asm) GVrs2_Gren)
                subgoal by auto  
                subgoal unfolding GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap apply auto  
                subgoal for a
                apply(subgoal_tac "a \<in> \<sigma> ` PVrs p") 
                  subgoal by (metis IntI PVrs_Pperm empty_iff)
                  subgoal unfolding bij_in_inv_Un_triv . . . .
               subgoal apply (auto simp: GVrs1_Gren GVrs2_Gren GVrs1_Gmap GVrs2_Gmap)
               by (metis (lifting) disjoint_iff inv_simp2)
               subgoal apply(subst Gmap_Gren')
               subgoal by auto subgoal  
               subgoal unfolding Gmap_comp  
               apply(rule sym) apply(rule Gmap_cong_id)
                 subgoal for ea unfolding o_def
                 apply(subst Eperm''_o[symmetric]) apply (cases ea) apply auto 
                 subgoal using Pperm_Pvalid by (auto simp: GSupp1_Gren GSupp1_Gmap GSupp2_Gmap)    
                 subgoal using Pperm_Pvalid by (auto simp: GSupp1_Gmap GSupp1_Gren subset_iff) . 
                 subgoal for ea unfolding o_def
                 apply(subst Eperm''_o[symmetric]) apply (cases ea)  
                 apply (auto simp: GSupp2_Gren GSupp2_Gmap subset_iff)
                   using Pperm_Pvalid apply auto  
  . . . . . . . . . . . .
               

lemma Ector_eq_imp_strong: 
"Ector u1 = Ector u2 \<Longrightarrow> |A| <o |UNIV::'a set| \<Longrightarrow> A \<inter> GVrs2 u1 = {} \<Longrightarrow>
   (\<exists>\<sigma> :: 'a :: covar_G \<Rightarrow> 'a. bij \<sigma> \<and> small \<sigma> \<and>
     id_on ((\<Union> (EVrs ` GSupp1 u1) - GVrs2 u1) \<union> A) \<sigma> \<and> 
     Gren id \<sigma> (Gmap (Eperm \<sigma>) id u1) = u2)"
sorry (* AtoD: Do we have a proof of this for datatypes? 
The one for codata should be identical. *)

lemma snd_single_Gmap: "snd ` GSupp1 u \<subseteq> {p} \<Longrightarrow> snd ` GSupp2 u \<subseteq> {p}
\<Longrightarrow> Gmap (\<lambda>(e,p'). (e,p)) (\<lambda>(e,p'). (e,p)) u = u"
apply(rule Gmap_cong_id) by auto

lemma snd_single_Gmap': 
assumes "snd ` GSupp1 u \<subseteq> {p}" "snd ` GSupp2 u \<subseteq> {p}"
shows "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) (Gmap fst fst u) = u"
apply(rule sym) apply(subst snd_single_Gmap[symmetric, of _ p])
  subgoal by fact subgoal by fact
  subgoal unfolding Gmap_comp o_def  
    by (meson Gmap_cong case_prod_beta) .


lemma 
(* dtorVrsGrenC: "dtorVrsGrenC Evalid' Edtor' Eperm'' EVrs''" *)
dtorVrsGrenC: "Evalid' ep \<Longrightarrow> Edtor' ep = Inr U \<Longrightarrow> 
     {u1,u2} \<subseteq> U \<Longrightarrow>
     \<exists>\<sigma>. bij (\<sigma>::'a::covar_G \<Rightarrow> 'a) \<and> |supp \<sigma>| <o |UNIV::'a set| \<and> 
         id_on ((\<Union>d' \<in> GSupp1 u1. EVrs'' d') - GVrs2 u1) \<sigma> \<and>
         Gren id \<sigma> (Gmap (Eperm'' \<sigma>) id u1) = u2"
apply (cases ep)
proof safe 
  fix e p 
  assume "Evalid' (e, p)"
  and 0: "Edtor' (e, p) = Inr U" and u12: "{u1, u2} \<subseteq> U"
  hence P: "Pvalid p" unfolding Evalid'_def by simp
  show "\<exists>\<sigma>. bij (\<sigma>::'a::covar_G \<Rightarrow> 'a) \<and> |supp \<sigma>| <o |UNIV::'a set| \<and> 
           id_on ((\<Union>d' \<in> GSupp1 u1. EVrs'' d') - GVrs2 u1) \<sigma> \<and>
           Gren id \<sigma> (Gmap (Eperm'' \<sigma>) id u1) = u2"
  proof(rule Ector_exhaust_fresh[OF PVrs_small, of p e, OF P])
    fix u assume e: "e = Ector u" and g: "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
    show ?thesis proof(cases "base u")
      case True
      show ?thesis using 0 unfolding e Edtor'_base[OF True] by simp
    next
      case False
      hence U: "Edtor1' (Ector u, p) = U" using 0 unfolding e Edtor'_step[OF False] by simp
      hence U: "U =
      {u1. Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and>
           GSupp1 (Gmap snd snd u1) \<subseteq> {p} \<and> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
           GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {}}"  
      unfolding Edtor1'_Ector[OF False P g] by auto

      hence u1: "Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
           "GSupp1 (Gmap snd snd u1) \<subseteq> {p}" "GSupp2 (Gmap snd snd u1) \<subseteq> {p}" "GVrs2 u1 \<inter> PVrs p = {}"
      and u2: "Ector (Gmap fst fst u2) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
          "GSupp1 (Gmap snd snd u2) \<subseteq> {p}" "GSupp2 (Gmap snd snd u2) \<subseteq> {p}" "GVrs2 u2 \<inter> PVrs p = {}"
      using u12 by auto

      have 00: "PVrs p \<inter> GVrs2 (Gmap fst fst u1) = {}" using u1 by (auto simp: GVrs2_Gmap)
      note eq = u1(1)[unfolded u2(1)[symmetric]]
      
      obtain \<sigma> where ss: "bij \<sigma> \<and> small \<sigma>"
        "id_on 
         ((\<Union> (EVrs ` GSupp1 (Gmap fst fst u1)) - GVrs2 (Gmap fst fst u1)) \<union> PVrs p )
         \<sigma>"
        "Gren id \<sigma> (Gmap (Eperm \<sigma>) id (Gmap fst fst u1)) = Gmap fst fst u2"   
        using Ector_eq_imp_strong[of "Gmap fst fst u1" "Gmap fst fst u2", OF eq PVrs_small 00, OF P]
        by blast
      have io: "\<And>e' p' a. (e',p') \<in> GSupp1 u1 \<Longrightarrow> a \<in> EVrs e' \<Longrightarrow> a \<notin> GVrs2 u1 \<Longrightarrow> \<sigma> a = a"
          "\<And>a. a \<in> PVrs p \<Longrightarrow> \<sigma> a = a" 
      using ss(2) unfolding id_on_def by (fastforce simp: GSupp1_Gmap GSupp2_Gmap GVrs2_Gmap)+

      show ?thesis proof(rule exI[of _ \<sigma>], safe)
        show "small \<sigma>" "bij \<sigma>" using ss by auto
      next
        show "id_on ((\<Union> (EVrs'' ` GSupp1 u1) - GVrs2 u1)) \<sigma>"
        unfolding id_on_def image_def proof(auto simp: EVrs''_def)
          fix a e' p' assume "(e', p') \<in> GSupp1 u1" "a \<in> EVrs e'" "a \<notin> GVrs2 u1" 
          thus "\<sigma> a = a" using io(1) by auto
        next
          fix a e' p' assume aa: "(e', p') \<in> GSupp1 u1" "a \<in> PVrs p'"  "a \<notin> GVrs2 u1"
          hence "p' = p" using u1(2) unfolding GSupp1_Gmap by auto  
          thus "\<sigma> a = a" using aa io(2) by auto
        qed
      next
        have ss3: "Gmap (Eperm \<sigma>) id (Gmap fst fst (Gren id \<sigma> u1)) = Gmap fst fst u2"
        unfolding ss(3)[symmetric] 
        by (simp add: Gmap_Gren'[symmetric] ss(1)) 

        have gg: "Gmap (Eperm'' \<sigma>) id (Gren id \<sigma> u1) = u2"
        apply(subst snd_single_Gmap'[symmetric, where t = u2 and p = p])
          subgoal by (metis GSupp1_Gmap u2(2))
          subgoal by (metis GSupp2_Gmap u2(3))
          subgoal apply(subst snd_single_Gmap'[symmetric, where t = "Gren id \<sigma> u1" and p = p])
            subgoal by (metis (no_types, opaque_lifting) GSupp1_Gmap GSupp1_Gren ss(1) supp_id_bound u1(2)) 
            subgoal  by (metis (no_types, lifting) GSupp2_Gmap GSupp2_Gren ss(1) supp_id_bound u1(3))
             subgoal unfolding ss3[symmetric] unfolding Gmap_comp unfolding o_def Eperm''_def
            apply(rule Gmap_cong)
              subgoal  by (simp add: P Pperm_cong_id io(2) ss(1))
              subgoal by simp . . .
        show "Gren id \<sigma> (Gmap (Eperm'' \<sigma>) id u1) = u2"
        unfolding gg[symmetric]  
        by (simp add: Gmap_Gren'[symmetric] ss(1)) 
      qed
    qed
  qed
qed

lemma step_Ector'_Ector_EVrs: 
"\<not> base u \<Longrightarrow> Pvalid p \<Longrightarrow> EVrs'' (Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p, p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctorVarsM_Ector'])
  subgoal .
  subgoal apply(rule tri_Un3) 
  by (auto simp: GVrs2_Gmap GSupp2_Gmap EVrs_Ector GSupp1_Gmap GVrs1_Gmap)
.

lemma base_Ector'_Ector_EVrs: 
"base u \<Longrightarrow> Pvalid p \<Longrightarrow> EVrs'' (Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p, p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctorVarsM_Ector'])
  subgoal .
  subgoal apply(rule tri_Un3) unfolding EVrs_Ector GSupp1_Gmap GVrs1_Gmap apply auto 
  by (auto simp: GVrs2_Gmap GSupp2_Gmap EVrs_Ector GSupp1_Gmap GVrs1_Gmap)
.

term Evalid'
(* lemma dtorVrsC: "dtorVrsC Evalid' Edtor' EVrs''" *)
lemma dtorVrsC_Inl: "Evalid' pe \<Longrightarrow>   
   Edtor' pe = Inl e1 \<Longrightarrow> EVrs e1 \<subseteq> EVrs'' pe"
unfolding EVrs''_def
unfolding Evalid'_def apply(cases pe) subgoal for e p apply simp 
apply(rule Ector_exhaust_fresh[OF PVrs_small, of p e])
  subgoal by simp  
  subgoal for u apply(cases "base u")
    subgoal using base_Ector'_Ector_EVrs unfolding Edtor'_base EVrs''_def 
    by (metis Edtor'_base Un_commute Un_subset_iff old.sum.inject(1))
    subgoal unfolding Edtor'_step using Edtor'_Inl_base by blast . . .

lemma dtorVrsC_Inr: "Evalid' pe \<Longrightarrow>   
   Edtor' pe = Inr U \<Longrightarrow> u\<in>U \<Longrightarrow> 
   GVrs1 u \<union> 
   (\<Union> {EVrs'' e - GVrs2 u | e . e \<in> GSupp1 u}) \<union> 
   (\<Union> {EVrs'' e | e . e \<in> GSupp2 u})
   \<subseteq> 
   EVrs'' pe"
unfolding EVrs''_def
unfolding Evalid'_def apply(cases pe) subgoal for e p apply simp 
apply(rule Ector_exhaust_fresh[OF PVrs_small, of p e])
  subgoal by simp  
  subgoal for v apply(cases "base v")
    subgoal unfolding Edtor'_base using Edtor'_Inr_step by auto
    subgoal apply clarify unfolding Edtor'_step  
    unfolding Edtor1'_Ector unfolding EVrs_Ector GSupp1_Gmap GSupp2_Gmap apply clarify
    apply(rule incl_Un_triv3)
    unfolding EVrs''_def EVrs_Ector 
    apply(rule subset_trans[OF _ Ector_Ector'_EVrs_step'[of p "Gmap fst fst u", unfolded GSupp1_Gmap 
      GSupp2_Gmap GVrs1_Gmap GVrs2_Gmap]]) 
      subgoal apply(rule incl_Un3_triv3)
        subgoal .. subgoal by auto subgoal by auto .
      subgoal .
      subgoal .
    subgoal using Edtor'_step in_Edtor1'_Ector by auto . . . .

(* lemma presDV_Evalid'_Edtor': "presDV Evalid' Edtor'" *)
lemma presDV_Evalid'_Edtor': "Evalid' ep \<Longrightarrow> Edtor' ep = Inr U \<Longrightarrow> u \<in> U \<Longrightarrow> 
  ep' \<in> GSupp1 u \<union> GSupp2 u 
   \<Longrightarrow> Evalid' ep'"
apply (cases ep) subgoal for e p apply simp
  unfolding Evalid'_def snd_conv apply(rule Ector_exhaust_fresh[OF PVrs_small, of p e])
    subgoal .
    subgoal for u apply(cases "base u")
      subgoal apply clarify unfolding Edtor'_base by auto
      subgoal apply clarify unfolding Edtor'_step Edtor1'_Ector 
      by (auto simp: GSupp1_Gmap GSupp2_Gmap) . . .
    
(* lemma presPV_Evalid'_Eperm'': "presPV Evalid' Eperm''" *)   
lemma presPV_Evalid'_Eperm'': 
"Evalid' ep \<Longrightarrow> small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> Evalid' (Eperm'' \<sigma> ep)"
apply (cases ep) subgoal for e p apply simp
unfolding Eperm''_def Evalid'_def by (simp add: Pperm_Pvalid) .

(*  *)

term "Corec Edtor' Eperm'' EVrs'' Evalid'"

theorem Bimodel_Corec: 
"Corec Edtor' Eperm'' EVrs'' Evalid'"
unfolding Corec_def apply(intro conjI)
  subgoal using Udtor_ne by blast
  subgoal using dtorVrsGrenC by blast
  subgoal using dtorPermC_Inl by blast
  subgoal using dtorPermC_Inr by blast
  subgoal using dtorVrsC_Inl by blast
  subgoal using dtorVrsC_Inr by blast
  subgoal using Eperm''_o Evalid'_def by auto
  subgoal by (metis NominalRel.Pperm_cong_id nomC)
  subgoal using presPV_Evalid'_Eperm'' by blast
  subgoal using presDV_Evalid'_Edtor' by blast .
  
end (* context *)


(**************) 
(* Binder codatatypes validate the 
birecursion principle: *)

term Corec
term Edtor'
term Eperm''
term EVrs''
term Evalid'

definition Edtor :: "('a::covar_G) E \<Rightarrow> (('a, 'a, 'a E,'a E) G) set" where 
"Edtor e = {u . Ector u = e}"

interpretation Expression_with_Birecursor Eperm EVrs "card_suc Gbd" Ector
proof (standard, safe)
  fix Pvalid :: "'p \<Rightarrow> bool"
  and Pperm :: "('a:: covar_G \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p"
  and PVrs :: "'p \<Rightarrow> 'a set"
  and Ector' :: "('a, 'a, 'p \<Rightarrow> 'a E, 'p \<Rightarrow> 'a E) G \<Rightarrow> 'p \<Rightarrow> 'a E"
  assume b: "Bimodel Pvalid Pperm PVrs Eperm EVrs (card_suc Gbd) Ector Ector'"

  define EEdtor' where "EEdtor' \<equiv> Edtor' PVrs Ector'"
  define EEdtor1' where "EEdtor1' \<equiv> Edtor1' PVrs Ector'"
  define EEperm'' where "EEperm'' \<equiv> Eperm'' Pperm"
  define EEVrs'' where "EEVrs'' \<equiv> EVrs'' PVrs"
  define EEvalid' :: "'a E \<times> 'p \<Rightarrow> bool" where "EEvalid' \<equiv> Evalid' Pvalid" 
  note EE_defs = EEdtor'_def EEdtor1'_def EEperm''_def EEVrs''_def EEvalid'_def
  note EE_rdefs = EE_defs[symmetric]


  interpret ccor: Corec EEdtor' EEperm'' EEVrs'' EEvalid'
  using Bimodel_Corec[OF b] unfolding EE_defs .
  find_theorems name: ccor name: COREC 
  define corec where "corec \<equiv> COREC.COREC ccor.Udtor' (Evalid' Pvalid)"
  note c = corec_def[symmetric]
  define crec where "crec \<equiv> curry corec"
  
  show "\<exists>rec. (\<forall>u p. Pvalid p \<and> noclashE u \<and> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> 
    rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and>
    (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV::'a::covar_G set| \<longrightarrow> Pvalid p \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
    (\<forall>e p. Pvalid p \<longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)"
  apply(rule exI[of _ crec], unfold noclashE_def, intro allI impI conjI)
    subgoal for u p apply(elim conjE) apply(cases "base u")
      subgoal 
      using ccor.COREC_DDTOR_Inl[of "(Ector u,p)", unfolded c]
      apply - unfolding EE_defs Edtor'_base[OF b] apply simp unfolding crec_def 
      apply simp 
      by (metis EEdtor'_def Evalid'_def b base_Gmap_eq corec_def snd_conv) 
      (* *)
      subgoal proof-
      assume f: "\<not> base u" and p: "Pvalid p"  and g : "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
      show "crec (Ector u) p = Ector' (Gmap crec crec u) p"
      proof-
         have "EEdtor' (Ector u, p) = Inr (EEdtor1' (Ector u, p))" 
         and 1: "Gmap corec corec ` (EEdtor1' (Ector u, p)) \<subseteq> Edtor (corec (Ector u, p))"
         using f p g apply(auto simp add: EE_defs Edtor'_step[OF b])  
         using EEdtor'_def EEvalid'_def Edtor'_step Edtor_def Evalid'_def b ccor.COREC_DDTOR_Inr corec_def
         by fastforce 
         hence 2: "\<And>v. Ector (Gmap fst fst v) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and>
          GSupp1 (Gmap snd snd v) \<union> GSupp2 (Gmap snd snd v) \<subseteq> {p} \<and> 
          GVrs2 v \<inter> PVrs p = {} \<and> GVrs2 v \<inter> GVrs1 v = {}
          \<Longrightarrow> Ector (Gmap corec corec v) = corec (Ector u, p)" 
         using f p g unfolding EE_defs Edtor_def Edtor1'_Ector  
         using in_Edtor1'_Ector[OF b] unfolding GSupp1_Gmap GSupp2_Gmap image_def 
         unfolding subset_iff by safe blast
         obtain w where w: "Ector w = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p" 
         and g1: "GVrs2 w \<inter> PVrs p = {}" "GVrs2 w \<inter> GVrs1 w = {}" 
         using Ector_fresh_surj'[OF Bimodel.PVrs_small[OF b p]] by metis
         show ?thesis unfolding crec_def apply simp apply(subst 2[symmetric, of "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) w"])
         apply safe
           subgoal unfolding Gmap_comp apply simp unfolding w ..
           subgoal unfolding GSupp1_Gmap by auto
           subgoal unfolding GSupp2_Gmap by auto
           subgoal using g1 unfolding GVrs2_Gmap by auto
           subgoal using g1 unfolding GVrs1_Gmap GVrs2_Gmap by auto
           subgoal using f unfolding Gmap_comp unfolding curry_def o_def
           apply(rule Bimodel.Ector_Ector'_Gmap[OF b]) using w p g g1 by auto . 
         qed 
       qed .
    subgoal for e p \<sigma> proof-
      assume assms : "Pvalid p" "small \<sigma>" "bij \<sigma>"
      show "crec (Eperm \<sigma> e) p = Eperm \<sigma> (crec e (Pperm (inv \<sigma>) p))"
      proof-
         have e: "EEvalid' (e,p)" using assms unfolding EE_defs Evalid'_def[OF b] by auto
         have "corec (EEperm'' \<sigma> (e,Pperm (inv \<sigma>) p)) = Eperm \<sigma> (corec (e,Pperm (inv \<sigma>) p))" 
         unfolding EE_defs using ccor.COREC_mmapD[OF assms(3,2) e] 
         unfolding corec_def
         unfolding EE_defs  
         by (metis EE_rdefs(3) EEdtor'_def EEvalid'_def Eperm''_def Evalid'_def assms(1,2,3) b bij_betw_inv_into
             ccor.COREC_mmapD ccor.valid_Umap snd_eqD supp_inv_bound) 
         thus ?thesis unfolding Eperm''_def crec_def curry_def using assms 
         by (smt (verit, del_insts) EEperm''_def EEvalid'_def Eperm''_def Evalid'_def b bij_betw_inv_into
               ccor.COREC_mmapD ccor.eq_Eperm_inv corec_def snd_conv supp_inv_bound) 
       qed
     qed 
   (* *)
   subgoal for e p  
   by (metis EEVrs''_def EE_rdefs(5) EVrs''_def 
        Evalid'_def Un_commute b c ccor.COREC_FFVarsD crec_def curry_def
         snd_conv) . 
qed
    
interpretation birec_codata: Expression_with_Birecursor_for_Subst_Strong Eperm EVrs "card_suc Gbd" Ector
  by standard

print_statement birec_codata.Esub_Strong.E_pbmv_axioms

end