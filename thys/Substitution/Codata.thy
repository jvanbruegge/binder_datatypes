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

interpretation Expression_with_Birecursor Eperm EVrs "card_suc Gbd" Ector
proof (standard, safe)
  fix Pvalid :: "'p \<Rightarrow> bool"
  and Pperm :: "('a \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p"
  and PVrs :: "'p \<Rightarrow> 'a set"
  and Ector' :: "('a, 'a, 'p \<Rightarrow> 'a E, 'p \<Rightarrow> 'a E) G \<Rightarrow> 'p \<Rightarrow> 'a E"
  assume "Bimodel Pvalid Pperm PVrs Eperm EVrs (card_suc Gbd) Ector Ector'"
  (* interpret corec: COREC  *)
  (* term corec.COREC *)
  show "\<exists>rec. (\<forall>u p. Pvalid p \<and> noclashE u \<and> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> 
    rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and>
    (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV| \<longrightarrow> Pvalid p \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
    (\<forall>e p. Pvalid p \<longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)"
    sorry
qed

interpretation birec_codata: Expression_with_Birecursor_for_Subst_Strong Eperm EVrs "card_suc Gbd" Ector
  by standard

print_statement birec_codata.Esub_Strong.E_pbmv_axioms

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

interpretation codata: Expression_with_Subst_Strong Eperm EVrs "card_suc Gbd" Ector Esub
  by standard (auto simp: Esub_Ector\<eta> Esub_Ector\<eta>' Esub_Ector EVrs_Esub Eperm_Esub)

print_statement codata.E_pbmv_axioms

end