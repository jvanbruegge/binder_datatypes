theory Data
  imports Expression_Like_Sub
begin

consts Gwit :: "('a1, 'a2, 'x1, 'x2) G"

definition "GMAP = (\<lambda>\<rho>1 \<rho>2 f1 f2 x. Gren \<rho>1 \<rho>2 (Gmap f1 f2 x))"

consts Grel :: "('x1 \<Rightarrow> 'x1' \<Rightarrow> bool) \<Rightarrow> ('x2 \<Rightarrow> 'x2' \<Rightarrow> bool) \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G \<Rightarrow> ('a1, 'a2, 'x1', 'x2') G \<Rightarrow> bool"

setup \<open>Sign.mandatory_path "G"\<close>

axiomatization where
  rel_compp: "\<And>R1 R2 S1 S2. Grel R1 R2 OO Grel S1 S2 \<le> Grel (R1 OO S1) (R2 OO S2)" and
  in_rel: "\<And>f1 f2 R1 R2 x y.
       |supp (f1 :: 'a1 \<Rightarrow> 'a1 :: var)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       bij f2 \<Longrightarrow>
       |supp (f2 :: 'a2 \<Rightarrow> 'a2 :: var)| <o |UNIV :: 'a2 set| \<Longrightarrow>
       Grel R1 R2 (GMAP f1 f2 id id x) y =
       (\<exists>z. (GSupp1 z \<subseteq> {(x, y). R1 x y} \<and> GSupp2 z \<subseteq> {(x, y). R2 x y}) \<and>
            GMAP id id fst fst z = x \<and> GMAP f1 f2 snd snd z = y)" and
  wit1: "GSupp1 Gwit = {}" and
  wit2: "GSupp2 Gwit = {}"
lemmas wit = G.wit1 G.wit2
setup \<open>Sign.parent_path\<close>

declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
mrbnf "('a1::var, 'a2::var, 'x1, 'x2) G"
  map: GMAP
  sets: free: GVrs1 bound: GVrs2 live: GSupp1 live: GSupp2
  bd: Gbd
  wits: Gwit
  rel: Grel
  var_class: var
                 apply (auto simp: GMAP_def Gren_def G.Sb_Inj G.Map_id fun_eq_iff G.infinite_regular_card_order G.wit
      G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
      G.Vrs_Sb G.Supp_Sb G.Vrs_Map G.Supp_Map G.Vrs_bd G.Supp_bd
      intro: trans[OF G.Sb_cong arg_cong[where f="Gsub _ _", OF G.Map_cong]]) [12]
     apply (rule G.rel_compp)
    apply (rule G.in_rel; assumption)
   apply (simp_all add: G.wit)
  done

binder_datatype (EVrs: 'a) E = Ector "('a, x::'a, t::'a E, 'a E) G" binds x in t
  for permute: Eperm
declare E.inject[simp del]

(*for technical reasons we now work with var_E_pre but the classes are the same*)
sublocale var_E_pre < var
  by (rule var_axioms)
sublocale var < var_E_pre
  by standard

instantiation Gbd_type :: var_E_pre begin
instance by standard
end

inductive subshape where
  "e \<in> GSupp1 u \<union> GSupp2 u \<Longrightarrow> subshape e (Ector u)"

lemma wfp_subshape: "wfp (subshape)"
  apply (rule wfpUNIVI)
  subgoal premises prems for P e
    apply (subgoal_tac "\<And>\<sigma> :: 'a \<Rightarrow> 'a. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> P (Eperm \<sigma> e)")
     apply (drule meta_spec[of _ id])
     apply (simp add: E.permute_id)
    apply (induct e)
    subgoal for u \<sigma>
      apply (rule prems[rule_format])
      apply (auto elim!: subshape.cases simp: G.set_map E.permute_comp  E.inject supp_comp_bound)
      done
    done
  done

lemma subshape_induct: "(\<And>e. (\<And>e'. subshape e' e \<Longrightarrow> P e') \<Longrightarrow> P e) \<Longrightarrow> P e"
  using wfp_subshape
  by (metis wfp_induct)

lemma E_coinduct_gen:
  fixes P and g :: "'k \<Rightarrow> 'a::var_E_pre E" and h e
  assumes "(\<And>k. P k \<Longrightarrow> g k = h k \<or>
    (\<exists>u. g k = Ector (GMAP id id g g u) \<and> h k = Ector (GMAP id id h h u) \<and>
    (\<forall>k \<in> GSupp1 u. P k) \<and> (\<forall>k \<in> GSupp2 u. P k)))"
  shows "P k \<Longrightarrow> g k = h k"
  apply (subgoal_tac "\<And>e. g k = e \<Longrightarrow> e = h k")
   apply blast
  subgoal for e
    apply (induct e arbitrary: k rule: subshape_induct)
    apply (drule assms)
    apply (erule disjE)
     apply simp
    apply (erule exE conjE)+
    apply (auto simp: G.map_comp G.set_map E.permute_id0  E.inject intro!: exI[of _ id] G.map_cong)
     apply (drule meta_spec2, drule meta_mp)
      apply (rule subshape.intros)
      apply (auto simp: E.permute_id0 G.set_map) []
     apply (drule meta_mp)
      apply (erule bspec)
      apply assumption
     apply simp
    apply (drule meta_spec2, drule meta_mp)
     apply (rule subshape.intros)
     apply (auto simp: E.permute_id0 G.set_map) []
    apply (drule meta_mp)
     apply (erule (1) bspec)
    apply simp
    done
  done

interpretation Expression_Strong Ector Eperm EVrs Gbd
  apply unfold_locales
  apply (auto simp: E.inject E.permute_id0 E.permute_comp E.FVars_permute GMAP_def Gren_def E.FVars_bd large'
    G.bd_card_order G.bd_cinfinite G.bd_regularCard intro: E.permute_cong_id)
  subgoal for A e
    apply (binder_induction e avoiding: A rule: E.strong_induct)
     apply assumption
    apply (rule exI conjI)+
     apply assumption
    apply (rule refl)
    done
  subgoal for P g h e
    apply (rule E_coinduct_gen[of P g h e]; simp add: GMAP_def Gren_def G.Sb_Inj)
    done
  done

context
  fixes \<delta> :: "'a \<Rightarrow> 'a :: var_E_pre" and \<rho> \<rho>' :: "'a ::var_E_pre \<Rightarrow> 'a E"
  assumes small_support:
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var_E_pre)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
begin

lemma permute_\<rho>:
  "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> = {} \<Longrightarrow> Eperm f (\<rho> a) = \<rho> (f a)"
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
  "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>' = {} \<Longrightarrow> Eperm f (\<rho>' a) = \<rho>' (f a)"
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
  "GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
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

interpretation data: Substitution_Strong Ector Eperm EVrs Gbd Esub
  by standard (auto simp: Esub_Ector\<eta> Esub_Ector\<eta>' Esub_Ector EVrs_Esub Eperm_Esub)

print_statement data.E_pbmv_axioms

end