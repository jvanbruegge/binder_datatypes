(* This theory proves that a a binder-datatype satisfies: 
Expression axiomatization, and, more strongly: 
-- the Expression_with_Surj_and_Coinduct axiomatization, 
and also 
-- the Expression_with_Birecursor axiomatization, 
and in particular to the Expression_with_Birecursor_for_Subst_Strong axioms.
*)

theory Data
imports 
Data_Customization 
begin
(*
lemma permute_\<rho>:
  "bij f \<Longrightarrow> |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> = {} \<Longrightarrow> Eperm f (\<rho> a) = \<rho> (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho> a = Ector (\<eta> a)")
    apply (simp add: GMAP_def Gren_def eta_natural)
   apply simp
   apply (rule E.permute_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
     apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho> a = Ector (\<eta> a)")
   apply (simp add: GMAP_def Gren_def eta_natural)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done

lemma permute_\<rho>':
  "bij f \<Longrightarrow> |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>' = {} \<Longrightarrow> Eperm f (\<rho>' a) = \<rho>' (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho>' a = Ector (\<eta>' a)")
    apply (simp add: GMAP_def Gren_def eta'_natural)
   apply simp
   apply (rule E.permute_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho>' a = Ector (\<eta>' a)")
   apply (simp add: GMAP_def Gren_def eta'_natural)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done
*)


(*****)

(* thm Expression_with_Birecursor_def Expression_with_Birecursor_axioms_def

context Expression_with_Birecursor  
begin 
*)

(**************)
(* Starting to prove that binder datatypes validate 
the birecursion principle: *)


context 
fixes Pvalid :: "'p \<Rightarrow> bool" 
and Pperm :: "('a::var_E_pre \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p" 
and PVrs :: "'p \<Rightarrow> 'a set" and 
Ector' :: "('a, 'a, 'p \<Rightarrow> 'a E, 'p \<Rightarrow> 'a E) G \<Rightarrow> 'p \<Rightarrow> 'a E"
assumes bimodel: "Bimodel Pvalid Pperm PVrs Eperm EVrs Gbd Ector Ector'"
begin 

(* Just getting all the Bomodel theorems *)
interpretation Bimodel Pvalid Pperm PVrs Eperm EVrs Gbd Ector Ector'
using bimodel .

(* *)

lemma snd_pair_comp: "snd \<circ> (\<lambda>(e, pu). (h e, f2 pu)) = (f2 o snd)"
unfolding fun_eq_iff by auto

theorem Bimodel_recE: 
"rec_E Pperm PVrs Pvalid {} Eperm EVrs
   (Ector' o Gmap snd snd) (\<lambda>_ . True)"
unfolding rec_E_def proof safe

  show 00: "P_axioms Pperm PVrs Pvalid {}"
  unfolding P_axioms_def
  using bimodel unfolding Bimodel_def NominalRel_def apply safe
    subgoal unfolding Pmap_comp_def by auto
    subgoal unfolding Pmap_id_def by auto
    subgoal unfolding PFVars_Pmap_def by auto
    subgoal unfolding PFVars_small_def by auto
    subgoal unfolding Pmap_validP_def by auto
    subgoal unfolding avset_small_def by auto .

  have 11: "Uctor_compat_validP Pvalid (Ector' \<circ> Gmap snd snd)"
  unfolding Uctor_compat_validP_def apply (auto simp: Gmap_comp snd_pair_comp) 
    unfolding Gmap_comp[symmetric]
    apply(rule Ector'_compat_Pvalid)
    by (auto simp: GSupp1_Gmap GSupp2_Gmap)

  show "U_axioms Pperm PVrs Pvalid {} Eperm EVrs (\<lambda>_. True)
     (Ector' \<circ> Gmap snd snd)"
  unfolding U_axioms_def apply safe
    subgoal using 11 .
    subgoal by (simp add: E.permute_comp0 Umap_comp_def)
    subgoal by (simp add: E.permute_cong_id Umap_cong_def)
    subgoal unfolding  Umap_Ector_def2[OF 11 00] apply auto 
    apply(subst Gmap_Gren'[symmetric])
      subgoal .  
      subgoal for f y p unfolding Gmap_comp unfolding snd_pair_comp
      unfolding Gmap_comp[symmetric]  
      apply(subst ctorPermM_Ector') by auto .
    subgoal unfolding UFVars_EFVars_def o_def apply(intro impI allI)
    apply(rule subset_trans[OF ctorVarsM_Ector'])  
      subgoal by simp
      subgoal for y p unfolding EVrs_Ector 
      by (fastforce simp: GVrs1_Gmap GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap) .
    subgoal unfolding validU_Umap_def by simp
    subgoal unfolding validU_Uctor_def by simp .
qed

(* NB: The above proof, which is essentially a proof that 
a bimodel is a model, has some complexity solely because 
the recursor is super-parameterized, it is a full recursor etc. *)

end (* context *)


(**************) 
(* Binder datatypes validate the 
birecursion principle: *)

interpretation Expression_with_Birecursor Eperm EVrs Gbd Ector
proof (standard, safe)
  fix Pvalid :: "'p \<Rightarrow> bool"
  and Pperm :: "('a \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p"
  and PVrs :: "'p \<Rightarrow> 'a set"
  and Ector' :: "('a, 'a, 'p \<Rightarrow> 'a E, 'p \<Rightarrow> 'a E) G \<Rightarrow> 'p \<Rightarrow> 'a E"
  assume b: "Bimodel Pvalid Pperm PVrs Eperm EVrs Gbd Ector Ector'"
  interpret rec: rec_E Pperm PVrs Pvalid "{}" Eperm EVrs
   "Ector' o Gmap snd snd" "\<lambda>_ . True"
  using Bimodel_recE[OF b] .
  term rec.recE
  show "\<exists>rec. 
    (\<forall>u p. Pvalid p \<and> noclashE u \<and> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> 
           rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and>
    (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow>
       |supp \<sigma>| <o |UNIV::'a set| \<longrightarrow> Pvalid p \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and>
       (\<forall>e p. Pvalid p \<longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)"
  apply(rule exI[of _ rec.recE]) apply(intro conjI allI)
    subgoal for u p using rec.rec_ctor[of p u] 
    by (auto simp: Gmap_comp o_def)  
    subgoal by (auto simp add: rec.recE_Eperm)
    subgoal using rec.recE_UFVars by auto .  
qed
  

interpretation birec_data: Expression_with_Birecursor_for_Subst_Strong Eperm EVrs Gbd Ector
  by standard

print_statement birec_data.Esub_Strong.E_pbmv_axioms

context
  fixes \<delta> :: "'a \<Rightarrow> 'a :: var_E_pre" and \<rho> \<rho>' :: "'a ::var_E_pre \<Rightarrow> 'a E"
  assumes small_support:
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var_E_pre)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
begin

interpretation Esub: QREC_fixed_E "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>'"
  "\<lambda>u. if \<exists>a. Rep_E_pre u = \<eta> a then \<rho> (SOME a. Rep_E_pre u = \<eta> a) else
       if \<exists>a. Rep_E_pre u = \<eta>' a then \<rho>' (SOME a. Rep_E_pre u = \<eta>' a) else
       Ector (GMAP \<delta> id snd snd (Rep_E_pre u))"
  apply standard
    apply (auto intro!: Un_bound simp: E.FVars_bd_UNIVs imsupp_supp_bound small_support) []
   apply (auto simp: map_E_pre_def set2_E_pre_def set3_E_pre_def set4_E_pre_def
      permute_\<rho> permute_\<rho>'
      Abs_E_pre_inverse GMAP_def Gren_def eta_natural eta'_natural small_support imsupp_commute[of _ \<delta>]
      G.Map_Sb[THEN fun_cong, simplified]
      G.Sb_comp[THEN fun_cong, simplified]
      G.Map_comp[THEN fun_cong, simplified] G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb
      Int_Un_distrib eta_distinct eta_distinct' eta_inject eta'_inject Ector_def[symmetric]
      dest: eta_inversion[rotated -1] eta'_inversion[rotated -1])
        apply (force simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def image_iff)
       apply (force simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def image_iff)
      apply (metis Un_iff image_eqI imsupp_def not_in_supp_alt)
     apply (metis Un_iff image_eqI imsupp_def not_in_supp_alt)
    apply (smt (verit, best) Un_iff fst_conv in_mono)
   apply (smt (verit, best) Un_iff fst_conv in_mono)
  apply (smt (verit, best) Un_iff fst_conv in_mono)
  done

definition "Esub = Esub.REC_E"

lemma
  Esub_Ector\<eta>: "Esub (Ector (\<eta> a)) = \<rho> a"
  and Esub_Ector\<eta>': "Esub (Ector (\<eta>' a)) = \<rho>' a"
  and Esub_Ector:
  "GVrs2 u \<inter> GVrs1 u = {} \<Longrightarrow> 
   GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
   GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  Esub (Ector u) = Ector (Gsub \<delta> id (Gmap Esub Esub u))"
    apply -
  unfolding Esub_def
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set2_E_pre_def Abs_E_pre_inverse noclash_E_def
        eta_distinct GMAP_def Gren_def eta_natural eta_inject)
    done
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set2_E_pre_def Abs_E_pre_inverse noclash_E_def
        eta_distinct' GMAP_def Gren_def eta'_natural eta'_inject)
    done
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set1_E_pre_def set2_E_pre_def set3_E_pre_def set4_E_pre_def
        GMAP_def Gren_def eta_distinct Abs_E_pre_inverse noclash_E_def small_support comp_def[of snd]
        G.Map_Sb[THEN fun_cong, simplified]
        G.Sb_comp[THEN fun_cong, simplified]
        G.Map_comp[THEN fun_cong, simplified]
        dest: eta_inversion[rotated -1] eta'_inversion[rotated -1])
      apply (metis (no_types, lifting) Gmap_eta' eta'_inversion eta'_natural
          small_support(1))
      subgoal by (metis (lifting) Gmap_eta eta_inversion eta_natural small_support(1))  
    done
  done

lemma EVrs_Esub: "EVrs (Esub e)
    \<subseteq> EVrs e \<union> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>')"
  unfolding Esub_def
  by (rule Esub.REC_FVars)

lemma Eperm_Esub: "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
  imsupp f \<inter> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>') = {} \<Longrightarrow>
  Eperm f (Esub t) = Esub (Eperm f t)"
  unfolding Esub_def
  by (rule Esub.REC_swap)

end

interpretation data: Expression_with_Subst_Strong Eperm EVrs Gbd Ector Esub
  by standard (auto simp: Esub_Ector\<eta> Esub_Ector\<eta>' Esub_Ector EVrs_Esub Eperm_Esub)

print_statement data.E_pbmv_axioms

end