theory Expression_Like_Sub
  imports Expression_Like_Strong Expression_Like_Eta
begin

locale Substitution = Expression +
  fixes Esub :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a ::var \<Rightarrow> 'e) \<Rightarrow> ('a ::var \<Rightarrow> 'e) \<Rightarrow> 'e \<Rightarrow> 'e"
  assumes
  Esub_Ector\<eta>:
  "\<And>\<delta> \<rho> \<rho>' a.
    |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
    Esub \<delta> \<rho> \<rho>' (Ector (\<eta> a)) = \<rho> a"
  and Esub_Ector\<eta>':
  "\<And>\<delta> \<rho> \<rho>' a.
    |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
    Esub \<delta> \<rho> \<rho>' (Ector (\<eta>' a)) = \<rho>' a"
  and Esub_Ector:
  "\<And>\<delta> \<rho> \<rho>' u.
    |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
  GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
  GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  Esub \<delta> \<rho> \<rho>' (Ector u) = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u))"
  and EVrs_Esub: "\<And>\<delta> \<rho> \<rho>' e. |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV::'a set| \<Longrightarrow> |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV::'a set| \<Longrightarrow>
    EVrs (Esub \<delta> \<rho> \<rho>' e) \<subseteq> EVrs e \<union> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>')"
  and Eperm_Esub: "\<And>\<delta> \<rho> \<rho>' \<sigma> e. |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV :: 'a set| \<Longrightarrow>
    |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow> |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
    bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> imsupp \<sigma> \<inter> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>') = {} \<Longrightarrow>
    Eperm \<sigma> (Esub \<delta> \<rho> \<rho>' e) = Esub \<delta> \<rho> \<rho>' (Eperm \<sigma> e)"

locale Substitution_Strong = Expression_Strong Ector Eperm EVrs Ebd + Substitution Ector Eperm EVrs Esub
  for Ector :: "('a :: var, 'a, 'e, 'e) G \<Rightarrow> 'e" and Eperm EVrs Ebd Esub
begin

lemma Esub_inversion0:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
   GVrs2 u \<inter> (imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e \<union> EVrs (Ector u)) = {} \<Longrightarrow>
   \<forall>a. e \<noteq> Ector (\<eta> a) \<Longrightarrow> \<forall>a. e \<noteq> Ector (\<eta>' a) \<Longrightarrow>
   \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a. u \<noteq> \<eta>' a \<Longrightarrow>
   Ector u = Esub \<delta> \<rho> \<rho>' e \<Longrightarrow> \<exists>u'. u = Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u') \<and> GVrs2 u' = GVrs2 u \<and> e = Ector u'"
  apply (insert Ector_fresh_surj[where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e \<union> EVrs (Ector u)" and e = e])
  apply (drule meta_mp)
   apply (auto intro!: Un_bound simp: imsupp_supp_bound) []
  apply (erule exE conjE)+
  apply (simp add: Int_Un_distrib Ector_eta_inj Ector_eta'_inj)
  apply (subst (asm) (2) Esub_Ector; (simp add: Int_Un_distrib Ector_eta_inj Ector_eta'_inj)?)
  apply (drule sym)
  subgoal for u'
    apply (subst (asm) Ector_fresh_inject[where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> (\<Union> (EVrs ` GSupp1 u') - GVrs2 u')"])
       apply (simp_all add: Int_Un_distrib G.Vrs_Sb G.Vrs_Map EVrs_Ector) [2]
     apply (auto intro!: Un_bound UN_bound card_of_minus_bound simp: imsupp_supp_bound ordLess_ordLeq_trans[OF G.Supp_bd(1) large']) []
    apply (erule exE conjE)+
    subgoal for \<sigma>
      apply (rule exI[where x = "Gren id \<sigma> (Gmap (Eperm \<sigma>) id u')"])
      apply (rule conjI)
       apply (erule trans[OF sym])
       apply (auto 0 0 simp add: Int_Un_distrib G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified] Eperm_Esub Ector_inject
          G.Vrs_Sb G.Vrs_Map Gren_def intro!: trans[OF G.Sb_cong arg_cong[where f = "Gsub _ _", OF G.Map_cong]] exI[of _ \<sigma>])
      apply (meson disjoint_iff_not_equal id_on_def not_in_imsupp_same)
      done
    done
  done

lemma Esub_inversion:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
   |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set| \<Longrightarrow>
   GVrs2 u \<inter> (imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e) = {} \<Longrightarrow>
   \<forall>a. e \<noteq> Ector (\<eta> a) \<Longrightarrow> \<forall>a. e \<noteq> Ector (\<eta>' a) \<Longrightarrow>
   \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a. u \<noteq> \<eta>' a \<Longrightarrow>
   Ector u = Esub \<delta> \<rho> \<rho>' e \<Longrightarrow> \<exists>u'. u = Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u') \<and> GVrs2 u' = GVrs2 u \<and> e = Ector u'"
  by (rule Esub_inversion0) (auto dest!: set_mp[OF EVrs_Esub, rotated -1])

inductive Efreee where 
  GVrs1: "a \<in> GVrs1 u \<Longrightarrow> \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow> Efreee a (Ector u)"
| GSupp1: "e \<in> GSupp1 u \<Longrightarrow> Efreee a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efreee a (Ector u)"
| GSupp2: "e \<in> GSupp2 u \<Longrightarrow> Efreee a e \<Longrightarrow> Efreee a (Ector u)"

binder_inductive (no_auto_equiv) Efreee
  where GVrs1 binds "GVrs2 u"
  | GSupp1 binds "GVrs2 u"
  | GSupp2 binds "GVrs2 u"
  for perms: _ Eperm | supps: _ and EVrs
           apply (auto simp: Eperm_id Eperm_comp[THEN fun_cong, simplified] EVrs_Eperm Eperm_cong[where \<tau>=id] G.Vrs_bd) [8]
  subgoal for R B \<sigma> a e
    apply (elim disj_forward exE conjE; hypsubst_thin)
    subgoal for _ u
      apply (rule exI[of _ "\<sigma> a"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map image_iff Eperm_Ector Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    done
  subgoal premises prems for R B a e
    apply (insert extend_fresh[where A = "{a} \<union> EVrs e" and B = B])
    apply (drule meta_mp) subgoal using prems(3) by auto
    apply (drule meta_mp) subgoal by (intro Un_bound; simp)
    apply (drule meta_mp) subgoal by simp
    apply (elim exE conjE)
    subgoal for \<sigma>
      apply (rule exI[of _ "\<sigma> ` B"])
      apply (rule conjI)
       apply simp
      apply (insert prems(3))
      apply (elim disj_forward exE conjE; hypsubst_thin)
      subgoal for _ u
        apply (rule exI[of _ a])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map Ector_inject EVrs_Ector Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
        done
      subgoal for e u _
        apply (rule exI[of _ "Eperm \<sigma> e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector id_onD[of _ \<sigma> a] Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2] prems(2)[of \<sigma> a e, rotated 2])
        done
      subgoal for e u _
        apply (rule exI[of _ "e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
        done
      done
    done
  done

inductive Efree\<eta> where 
  eta: "Efree\<eta> a (Ector (\<eta> a))"
| GSupp1: "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree\<eta> a (Ector u)"
| GSupp2: "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> Efree\<eta> a (Ector u)"

binder_inductive (no_auto_equiv) Efree\<eta>
  where GSupp1 binds "GVrs2 u"
  | GSupp2 binds "GVrs2 u"
  for perms: _ Eperm | supps: _ and EVrs
          apply (auto simp: Eperm_id Eperm_comp[THEN fun_cong, simplified] EVrs_Eperm Eperm_cong[where \<tau>=id] G.Vrs_bd Eperm_Ector eta_natural) [7]
  subgoal for R B \<sigma> a e
    apply (elim disj_forward exE conjE; hypsubst_thin)
    subgoal for _
      apply (auto simp: Eperm_Ector eta_natural Gren_def)
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    done
  subgoal premises prems for R B a e
    apply (insert extend_fresh[where A = "{a} \<union> EVrs e" and B = B])
    apply (drule meta_mp) subgoal using prems(3) by auto
    apply (drule meta_mp) subgoal by (intro Un_bound; simp)
    apply (drule meta_mp) subgoal by simp
    apply (elim exE conjE)
    subgoal for \<sigma>
      apply (rule exI[of _ "\<sigma> ` B"])
      apply (rule conjI)
       apply simp
      apply (insert prems(3))
      apply (elim disj_forward exE conjE; hypsubst_thin)
      subgoal for _
        apply auto
        done
      subgoal for e u _
        apply (rule exI[of _ "Eperm \<sigma> e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector id_onD[of _ \<sigma> a] Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2] prems(2)[of \<sigma> a e, rotated 2])
        done
      subgoal for e u _
        apply (rule exI[of _ "e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
        done
      done
    done
  done

inductive Efree\<eta>' where 
  eta': "Efree\<eta>' a (Ector (\<eta>' a))"
| GSupp1: "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree\<eta>' a (Ector u)"
| GSupp2: "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> Efree\<eta>' a (Ector u)"

binder_inductive (no_auto_equiv) Efree\<eta>'
  where GSupp1 binds "GVrs2 u"
  | GSupp2 binds "GVrs2 u"
  for perms: _ Eperm | supps: _ and EVrs
          apply (auto simp: Eperm_id Eperm_comp[THEN fun_cong, simplified] EVrs_Eperm Eperm_cong[where \<tau>=id] G.Vrs_bd Eperm_Ector eta_natural) [7]
  subgoal for R B \<sigma> a e
    apply (elim disj_forward exE conjE; hypsubst_thin)
    subgoal for _
      apply (auto simp: Eperm_Ector eta'_natural Gren_def)
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    subgoal for e' u _
      apply (rule exI[of _ "Eperm \<sigma> e'"])
      apply (rule exI[of _ "Gsub \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u)"])
      apply (rule exI[of _ "\<sigma> a"])
      apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map image_iff Eperm_Ector
          Eperm_comp[THEN fun_cong, simplified] Eperm_id bij_implies_inject Gren_def
          dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
      done
    done
  subgoal premises prems for R B a e
    apply (insert extend_fresh[where A = "{a} \<union> EVrs e" and B = B])
    apply (drule meta_mp) subgoal using prems(3) by auto
    apply (drule meta_mp) subgoal by (intro Un_bound; simp)
    apply (drule meta_mp) subgoal by simp
    apply (elim exE conjE)
    subgoal for \<sigma>
      apply (rule exI[of _ "\<sigma> ` B"])
      apply (rule conjI)
       apply simp
      apply (insert prems(3))
      apply (elim disj_forward exE conjE; hypsubst_thin)
      subgoal for _
        apply auto
        done
      subgoal for e u _
        apply (rule exI[of _ "Eperm \<sigma> e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector id_onD[of _ \<sigma> a] Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2] prems(2)[of \<sigma> a e, rotated 2])
        done
      subgoal for e u _
        apply (rule exI[of _ "e"])
        apply (rule exI[of _ "Gsub id \<sigma> (Gmap (Eperm \<sigma>) id u)"])
        apply (rule exI[of _ a])
        apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Ector_inject EVrs_Ector Gren_def
            intro!: exI[of _ \<sigma>] elim!: id_on_antimono
            dest: eta_inversion[rotated 2] eta'_inversion[rotated 2])
        done
      done
    done
  done

definition "EFVrs e = {a. Efreee a e}"
definition "EFVrs\<eta> e = {a. Efree\<eta> a e}"
definition "EFVrs\<eta>' e = {a. Efree\<eta>' a e}"

lemma Esub_unique_fresh:
  assumes
    "|A| <o |UNIV::'a set|"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'e)| <o |UNIV::'a set|"
    "\<And>a. h (Ector (\<eta> a)) = \<rho> a"
    "\<And>a. h (Ector (\<eta>' a)) = \<rho>' a"
    "\<And>u.
  GVrs2 u \<inter> A = {} \<Longrightarrow>
  GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
  GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  h (Ector u) = Ector (Gsub \<delta> id (Gmap h h u))"
  shows
    "h = Esub \<delta> \<rho> \<rho>'"
  apply (rule ext)
  subgoal for e
    apply (rule E_coinduct[where g=h and h="Esub \<delta> \<rho> \<rho>'" and P="\<lambda>_. True"])
     apply simp_all
    subgoal for e
      apply (insert Ector_fresh_surj[where e = "e" and A = "
         imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>' \<union> EVrs e \<union> A"])
      apply (drule meta_mp)
       apply (auto intro!: Un_bound IImsupp_bound simp: imsupp_supp_bound assms) []
      apply (simp add: Int_Un_distrib)
      apply (erule exE conjE)+
      subgoal for u
        apply (cases "\<exists>a. u = \<eta> a")
         apply (auto simp: Esub_Ector\<eta> assms) []
        apply (cases "\<exists>a. u = \<eta>' a")
         apply (auto simp: Esub_Ector\<eta>' assms) []
        apply (rule disjI2)
        apply (rule exI[where x="Gsub \<delta> id u"])
        apply (auto simp: assms Esub_Ector G.Map_Sb[THEN fun_cong, simplified])
        done
      done
    done
  done

lemma SSupp_comp_Esub_le:
  assumes "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "SSupp (Ector \<circ> \<eta>) (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'') \<subseteq>
   SSupp (Ector \<circ> \<eta>) \<rho>'' \<union> SSupp (Ector \<circ> \<eta>) \<rho>"
    "SSupp (Ector \<circ> \<eta>') (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'') \<subseteq>
   SSupp (Ector \<circ> \<eta>') \<rho>'' \<union> SSupp (Ector \<circ> \<eta>') \<rho>'"
  using assms
  by (auto simp: SSupp_def Esub_Ector\<eta> Esub_Ector\<eta>')

lemma SSupp_comp_bound[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>''| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'')| <o |UNIV :: 'a set|"
  apply (rule ordLeq_ordLess_trans)
   apply (erule (2) card_of_mono1[OF SSupp_comp_Esub_le(1)])
  apply (auto simp: Un_bound)
  done

lemma SSupp_comp_bound'[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>''| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'')| <o |UNIV :: 'a set|"
  apply (rule ordLeq_ordLess_trans)
   apply (erule (2) card_of_mono1[OF SSupp_comp_Esub_le(2)])
  apply (auto simp: Un_bound)
  done

lemma EFVrs\<eta>_Ector_eta: "EFVrs\<eta> (Ector (\<eta> a)) = {a}"
  unfolding EFVrs\<eta>_def
  apply (auto intro: Efree\<eta>.intros)
  subgoal for x
    apply (induct "Ector (\<eta> a)" rule: Efree\<eta>.induct)
      apply (auto simp: Ector_eta_inj dest: eta_inj)
    done
  done

lemma EFVrs\<eta>'_Ector_eta': "EFVrs\<eta>' (Ector (\<eta>' a)) = {a}"
  unfolding EFVrs\<eta>'_def
  apply (auto intro: Efree\<eta>'.intros)
  subgoal for x
    apply (induct "Ector (\<eta>' a)" rule: Efree\<eta>'.induct)
      apply (auto simp: Ector_eta'_inj dest: eta'_inj)
    done
  done

lemma Efree_alt:
  "Efreee a e \<longleftrightarrow> a \<in> EFVrs e"
  "Efree\<eta> a e \<longleftrightarrow> a \<in> EFVrs\<eta> e"
  "Efree\<eta>' a e \<longleftrightarrow> a \<in> EFVrs\<eta>' e"
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def by auto

lemma Efreee_Efree: "Efreee a e \<Longrightarrow> a \<in> EVrs e"
  by (induct e rule: Efreee.induct) (auto simp: EVrs_Ector)
lemma Efree\<eta>_Efree: "Efree\<eta> a e \<Longrightarrow> a \<in> EVrs e"
  by (induct e rule: Efree\<eta>.induct) (auto simp: EVrs_Ector)
lemma Efree\<eta>'_Efree: "Efree\<eta>' a e \<Longrightarrow> a \<in> EVrs e"
  by (induct e rule: Efree\<eta>'.induct) (auto simp: EVrs_Ector)

lemma EFVrs_bd:
  "|EFVrs (x :: 'e)| <o Ebd"
  "|EFVrs\<eta> (x :: 'e)| <o Ebd"
  "|EFVrs\<eta>' (x :: 'e)| <o Ebd"
  apply (meson EVrs_bd Efree_alt(1) Efreee_Efree card_of_mono1 ordLeq_ordLess_trans subsetI)
  apply (meson EVrs_bd Efree_alt(2) Efree\<eta>_Efree card_of_mono1 ordLeq_ordLess_trans subsetI)
  apply (meson EVrs_bd Efree_alt(3) Efree\<eta>'_Efree card_of_mono1 ordLeq_ordLess_trans subsetI)
  done

lemma EFVrs_bound[simp]:
  "|EFVrs (x :: 'e)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta> (x :: 'e)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta>' (x :: 'e)| <o |UNIV :: 'a set|"
  using EFVrs_bd Ebd_le ordLess_ordLeq_trans by blast+

lemma EFVrs_EsubI1[OF _ _ _ _ refl]:
  assumes
    "z \<in> EFVrs e"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "\<delta> z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,5) unfolding EFVrs_def mem_Collect_eq
  apply (binder_induction z e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efreee.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
    apply hypsubst_thin
  subgoal for a u
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
    apply (rule Efreee.intros)
      apply (simp add: G.Vrs_Sb G.Vrs_Map assms(2-4))
    subgoal by (meson eta_inversion assms(2) supp_id_bound)
    subgoal by (meson eta'_inversion assms(2) supp_id_bound)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
      apply fastforce
     apply fastforce
    apply (rule Efreee.intros(2))
      apply (simp add: G.Supp_Sb G.Supp_Map assms(2-4))
      apply (erule imageI)
     apply assumption
    apply (simp add: G.Vrs_Sb G.Vrs_Map assms(2-4))
    apply (metis imsupp_empty_IntD1)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
      apply fastforce
     apply fastforce
    apply (rule Efreee.intros(3))
     apply (simp add: G.Supp_Sb G.Supp_Map assms(2-4))
     apply (erule imageI)
    apply assumption
    done
  done

lemma EFVrs_EsubI2[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs_def EFVrs\<eta>_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efreee.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (metis (no_types, lifting) Ector_eta_inj Efreee.cases GSupp_eta(1,2) empty_iff)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EVrs \<rho>")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efreee_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efreee.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs_EsubI3[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs_def EFVrs\<eta>'_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>'.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>'; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efreee.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (metis (no_types, lifting) Ector_eta'_inj Efreee.cases GSupp_eta'(1,2) empty_iff)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>'_def Efreee_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efreee.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs_EsubD:
  assumes
    "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> \<delta> ` EFVrs e \<union>
  ((\<Union>x\<in>EFVrs\<eta> e. EFVrs (\<rho> x)) \<union>
   (\<Union>x\<in>EFVrs\<eta>' e. EFVrs (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (binder_induction z "Esub \<delta> \<rho> \<rho>' e" arbitrary: e avoiding:
      "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e"
      rule: Efreee.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a u e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(1) Efreee.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1) Efreee.intros(1))
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply blast
       apply blast
      apply blast
     apply blast
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Vrs_Sb)
    unfolding G.Vrs_Map
    using Efreee.intros(1) by fastforce
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efreee.intros(2) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efreee.intros(2) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
        apply (smt (verit, del_insts) Efreee.intros(2)
          Un_empty image_iff imsupp_empty_IntD1 mem_Collect_eq)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (cases "\<rho> a = Ector (\<eta> a)")
         apply (metis (no_types, lifting) Ector_eta_inj Efreee.cases GSupp_eta(1,2) empty_iff)
        apply (smt (verit, ccfv_threshold) Efree\<eta>.intros(2) IImsupp'_def SSupp_def Un_iff comp_apply
            disjoint_iff_not_equal mem_Collect_eq)
        done
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (cases "\<rho>' a = Ector (\<eta>' a)")
         apply (metis (no_types, lifting) Ector_eta'_inj Efreee.cases GSupp_eta'(1,2) empty_iff)
        apply (smt (verit, ccfv_threshold) Efree\<eta>'.intros(2) IImsupp'_def SSupp_def Un_iff comp_apply
            disjoint_iff_not_equal mem_Collect_eq)
        done
      done
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efreee.intros(3) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efreee.intros(3) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    apply (elim disj_forward ex_forward; assumption?)
      apply (smt (verit, del_insts) Efreee.intros(3)
        Un_empty image_iff imsupp_empty_IntD1 mem_Collect_eq)
     apply (metis Efree\<eta>.intros(3))
    apply (metis Efree\<eta>'.intros(3))
    done
  done

lemma EFVrs\<eta>_EsubI2[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs\<eta> (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs\<eta>_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (simp add: EFVrs\<eta>_Ector_eta Efree_alt(2))
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EVrs \<rho>")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efree\<eta>_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs\<eta>_EsubI3[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs\<eta> (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>'.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>'; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (metis (no_types, lifting) Ector_eta'_inj Efree\<eta>.cases GSupp_eta'(1,2) empty_iff eta_distinct)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>'_def Efree\<eta>_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs\<eta>_EsubD:
  assumes
    "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> ((\<Union>x\<in>EFVrs\<eta> e. EFVrs\<eta> (\<rho> x)) \<union> (\<Union>x\<in>EFVrs\<eta>' e. EFVrs\<eta> (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (binder_induction z "Esub \<delta> \<rho> \<rho>' e" arbitrary: e avoiding:
      "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e"
      rule: Efree\<eta>.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1) Efree\<eta>.intros(1))
    apply (insert Ector_fresh_surj[of "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e" e, simplified])
    apply (drule meta_mp)
     apply (auto simp: assms imsupp_supp_bound Un_bound) []
    apply (auto simp: Ector_eta_inj Ector_eta'_inj Esub_Ector Int_Un_distrib assms(2-4))
    apply (metis (no_types, lifting) Ector_eta_inj assms(2) eta_inversion supp_id_bound)
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(2) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>.intros(2) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
       apply (metis (mono_tags, lifting) EFVrs\<eta>_Ector_eta Efree\<eta>.GSupp1 Efree_alt(2) IImsupp'_def
          Int_emptyD SSupp_def Un_iff comp_apply mem_Collect_eq singletonD)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (smt (verit, ccfv_threshold) Ector_eta'_inj' Efree\<eta>'.GSupp1 Efree\<eta>.simps
            GSupp_eta'(1,2) IImsupp'_def SSupp_def Un_iff all_not_in_conv comp_apply disjoint_iff
            eta_distinct mem_Collect_eq)
        done
      done
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(3) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>.intros(3) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    apply (elim disj_forward ex_forward; assumption?)
     apply (metis Efree\<eta>.intros(3))
    apply (metis Efree\<eta>'.intros(3))
    done
  done

lemma EFVrs\<eta>'_EsubI2[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs\<eta>' (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (metis (no_types, lifting) Ector_eta_inj Efree\<eta>'.cases GSupp_eta(1,2) empty_iff eta_distinct)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EVrs \<rho>")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>'_def Efree\<eta>'_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs\<eta>'_EsubI3[OF _ _ _ _ _ refl]:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs\<eta>' (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
    "e' = e"
  shows "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2,6) unfolding EFVrs\<eta>'_def mem_Collect_eq
  apply (binder_induction a e arbitrary: e' avoiding: "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e'" rule: Efree\<eta>'.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a
    apply (subst Esub_Ector\<eta>'; (simp add: Int_Un_distrib assms(3-5))?)
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5) IImsupp'_def)?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (simp add: EFVrs\<eta>'_Ector_eta' Efree_alt(3))
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply fast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>'_def Efree\<eta>'_Efree intro!: exI[of _ a]) []
    done
  subgoal for e' u a
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    done
  done

lemma EFVrs\<eta>'_EsubD:
  assumes
    "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> ((\<Union>x\<in>EFVrs\<eta> e. EFVrs\<eta>' (\<rho> x)) \<union> (\<Union>x\<in>EFVrs\<eta>' e. EFVrs\<eta>' (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (binder_induction z "Esub \<delta> \<rho> \<rho>' e" arbitrary: e avoiding:
      "imsupp \<delta>" "IImsupp' (Ector o \<eta>) EVrs \<rho>" "IImsupp' (Ector o \<eta>') EVrs \<rho>'" "EVrs e"
      rule: Efree\<eta>'.strong_induct)
        apply (auto simp: assms imsupp_supp_bound) [4]
  subgoal for a e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>.intros(1) Efree\<eta>'.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1))
    apply (insert Ector_fresh_surj[of "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>' \<union> EVrs e" e, simplified])
    apply (drule meta_mp)
     apply (auto simp: assms imsupp_supp_bound Un_bound) []
    apply (auto simp: Ector_eta_inj Ector_eta'_inj Esub_Ector Int_Un_distrib assms(2-4))
    apply (metis (no_types, lifting) Ector_eta'_inj assms(2) eta'_inversion supp_id_bound)
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>'.intros(2) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(2) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
       apply (smt (verit, ccfv_threshold) Ector_eta_inj Efree\<eta>'.simps Efree\<eta>.intros(2)
          GSupp_eta(1,2) GVrs_eta'(1) GVrs_eta(1) IImsupp'_def SSupp_def Un_iff comp_apply
          disjoint_iff disjoint_single empty_iff mem_Collect_eq)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (metis (mono_tags, lifting) EFVrs\<eta>'_Ector_eta' Efree\<eta>'.GSupp1 Efree_alt(3) IImsupp'_def
            Int_Un_distrib Int_emptyD SSupp_def Un_empty comp_apply mem_Collect_eq singletonD)
        done
      done
    done
  subgoal for e' u b e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector\<eta> assms(2-4)) []
     apply (metis Efree\<eta>'.intros(3) eta)
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector\<eta>' assms(2-4)) []
     apply (metis Efree\<eta>'.intros(3) eta')
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
         apply (simp add: Int_Un_distrib)
        apply force
       apply force
      apply force
     apply force
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    apply (elim disj_forward ex_forward; assumption?)
     apply (metis Efree\<eta>.intros(3))
    apply (metis Efree\<eta>'.intros(3))
    done
  done

lemma E_pbmv_axioms:
  "infinite_regular_card_order Ebd"
  "Esub id (Ector \<circ> \<eta>) (Ector \<circ> \<eta>') = id"
  "\<And>f \<rho>1 \<rho>2.
       |supp (f :: 'a :: var \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
       Esub f \<rho>1 \<rho>2 \<circ> (Ector \<circ> \<eta>) = \<rho>1"
  "\<And>f \<rho>1 \<rho>2.
       |supp (f :: 'a :: var \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
       Esub f \<rho>1 \<rho>2 \<circ> (Ector \<circ> \<eta>') = \<rho>2"
  "\<And>g \<rho>'1 \<rho>'2 f \<rho>1 \<rho>2.
       |supp (f :: 'a :: var \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
       |supp g| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>) \<rho>'1| <o |UNIV :: 'a set| \<Longrightarrow>
       |SSupp (Ector \<circ> \<eta>') \<rho>'2| <o |UNIV :: 'a set| \<Longrightarrow>
       Esub g \<rho>'1 \<rho>'2 \<circ> Esub f \<rho>1 \<rho>2 =
       Esub (g \<circ> f) (Esub g \<rho>'1 \<rho>'2 \<circ> \<rho>1) (Esub g \<rho>'1 \<rho>'2 \<circ> \<rho>2)"
  "\<And>x. |EFVrs x| <o Ebd"
  "\<And>x. |EFVrs\<eta> x| <o Ebd"
  "\<And>x. |EFVrs\<eta>' x| <o Ebd"
  "\<And>a. EFVrs ((Ector \<circ> \<eta>) a) = {}"
  "\<And>a. EFVrs ((Ector \<circ> \<eta>') a) = {}"
  "\<And>a. EFVrs\<eta> ((Ector \<circ> \<eta>) a) = {a}"
  "\<And>a. EFVrs\<eta> ((Ector \<circ> \<eta>') a) = {}"
  "\<And>a. EFVrs\<eta>' ((Ector \<circ> \<eta>) a) = {}"
  "\<And>a. EFVrs\<eta>' ((Ector \<circ> \<eta>') a) = {a}"
  "\<And>f \<rho>1 \<rho>2 x.
        |supp (f :: 'a :: var \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs (Esub f \<rho>1 \<rho>2 x) =
        f ` EFVrs x \<union>
        ((\<Union>x\<in>EFVrs\<eta> x. EFVrs (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs (\<rho>2 x)))"
  "\<And>f \<rho>1 \<rho>2 x.
        |supp (f :: 'a :: var \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs\<eta> (Esub f \<rho>1 \<rho>2 x) =
        (\<Union>x\<in>EFVrs\<eta> x. EFVrs\<eta> (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs\<eta> (\<rho>2 x))"
  "\<And>f \<rho>1 \<rho>2 x.
        |supp (f :: 'a :: var \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        EFVrs\<eta>' (Esub f \<rho>1 \<rho>2 x) =
        (\<Union>x\<in>EFVrs\<eta> x. EFVrs\<eta>' (\<rho>1 x)) \<union> (\<Union>x\<in>EFVrs\<eta>' x. EFVrs\<eta>' (\<rho>2 x))"
  "\<And>f \<rho>1 \<rho>2 g \<rho>'1 \<rho>'2 x.
        |supp (f :: 'a :: var \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>2| <o |UNIV :: 'a set| \<Longrightarrow>
        |supp g| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>) \<rho>'1| <o |UNIV :: 'a set| \<Longrightarrow>
        |SSupp (Ector \<circ> \<eta>') \<rho>'2| <o |UNIV :: 'a set| \<Longrightarrow>
        (\<And>a. a \<in> EFVrs x \<Longrightarrow> f a = g a) \<Longrightarrow>
        (\<And>a. a \<in> EFVrs\<eta> x \<Longrightarrow> \<rho>1 a = \<rho>'1 a) \<Longrightarrow>
        (\<And>a. a \<in> EFVrs\<eta>' x \<Longrightarrow> \<rho>2 a = \<rho>'2 a) \<Longrightarrow>
        Esub f \<rho>1 \<rho>2 x = Esub g \<rho>'1 \<rho>'2 x"
  subgoal
    by (rule Ebd_infinite_regular_card_order)
  subgoal
    apply (rule Esub_unique_fresh[symmetric, where A="{}"])
          apply (simp_all add: G.Sb_Inj G.Map_id)
    done
  subgoal for \<delta> \<rho> \<rho>'
    by (simp add: fun_eq_iff Esub_Ector\<eta>)
  subgoal
    by (simp add: fun_eq_iff Esub_Ector\<eta>')
  subgoal for \<delta>1 \<rho>1 \<rho>1' \<delta>2 \<rho>2 \<rho>2'
    apply (rule Esub_unique_fresh[where A = "imsupp \<delta>1 \<union> imsupp \<delta>2 \<union>
   IImsupp' (Ector o \<eta>) EVrs \<rho>1 \<union> IImsupp' (Ector o \<eta>) EVrs \<rho>2 \<union>
   IImsupp' (Ector o \<eta>') EVrs \<rho>1' \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>2'"])
          apply (simp_all add: supp_comp_bound Esub_Ector\<eta> Esub_Ector\<eta>' Esub_Ector Un_bound
        imsupp_supp_bound Int_Un_distrib)
    apply (subst Esub_Ector;
        (simp add: EVrs_Ector G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map Int_Un_distrib G.Map_comp[THEN fun_cong, simplified]
          G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified])?)
      apply (rule conjI)
       apply (metis Int_commute Int_image_imsupp)
    subgoal for u
      apply safe
      apply (drule set_mp[OF EVrs_Esub, rotated -1]; simp?)
      apply fast
      done
    subgoal by (meson eta_inversion supp_id_bound)
    subgoal by (meson eta'_inversion supp_id_bound)
    done
  subgoal by (rule EFVrs_bd)
  subgoal by (rule EFVrs_bd)
  subgoal by (rule EFVrs_bd)
  subgoal for x
    by (auto simp: EFVrs_def Ector_eta_inj' elim: Efreee.cases)
  subgoal for x
    by (auto simp: EFVrs_def Ector_eta'_inj' elim: Efreee.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>_def Ector_eta_inj' eta_inj elim: Efree\<eta>.cases intro: Efree\<eta>.intros)
  subgoal for x
    by (auto simp: EFVrs\<eta>_def Ector_eta'_inj' eta_distinct elim: Efree\<eta>.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>'_def Ector_eta_inj' dest!: eta_distinct[THEN notE, OF sym] elim: Efree\<eta>'.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>'_def Ector_eta'_inj' eta'_inj elim: Efree\<eta>'.cases intro: Efree\<eta>'.intros)
  subgoal for \<delta> \<rho> \<rho>' x
    by (auto intro: EFVrs_EsubI1 EFVrs_EsubI2 EFVrs_EsubI3 dest: EFVrs_EsubD)
  subgoal for \<delta> \<rho> \<rho>' x
    by (auto intro: EFVrs\<eta>_EsubI2 EFVrs\<eta>_EsubI3 dest: EFVrs\<eta>_EsubD)
  subgoal for \<delta> \<rho> \<rho>' x 
    by (auto intro: EFVrs\<eta>'_EsubI2 EFVrs\<eta>'_EsubI3 dest: EFVrs\<eta>'_EsubD)
  subgoal for \<delta>1 \<rho>1 \<rho>1' \<delta>2 \<rho>2 \<rho>2' e
    apply (rule E_coinduct[where g="Esub \<delta>1 \<rho>1 \<rho>1'" and h="Esub \<delta>2 \<rho>2 \<rho>2'" and e = e
          and P = "\<lambda>e. (\<forall>a \<in> EFVrs e. \<delta>1 a = \<delta>2 a) \<and> (\<forall>a \<in> EFVrs\<eta> e. \<rho>1 a = \<rho>2 a) \<and> (\<forall>a \<in> EFVrs\<eta>' e. \<rho>1' a = \<rho>2' a)", rotated -1])
     apply blast
    subgoal premises prems for e
      thm prems
      apply (insert prems(1-6,10-))
      apply (cases "\<exists>a. e = Ector (\<eta> a)")
       apply (auto simp: Esub_Ector\<eta> EFVrs\<eta>_Ector_eta) []
      apply (cases "\<exists>a. e = Ector (\<eta>' a)")
       apply (auto simp: Esub_Ector\<eta>' EFVrs\<eta>'_Ector_eta') []
      apply (rule disjI2)
      apply (insert Ector_fresh_surj[where e = "e" and A = "
         imsupp \<delta>1 \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>1 \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>1' \<union>
         imsupp \<delta>2 \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>2 \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>2' \<union> EVrs e"])
      apply (drule meta_mp)
       apply (auto intro!: Un_bound IImsupp_bound simp: imsupp_supp_bound) []
      apply (simp add: Int_Un_distrib)
      apply (erule exE conjE)+
      apply hypsubst_thin
      subgoal for u
        apply (rule exI[where x="Gsub \<delta>2 id u"])
        apply (simp add: G.Supp_Sb Esub_Ector Ector_eta_inj Ector_eta'_inj
            G.Map_Sb[THEN fun_cong, simplified])
        apply (intro conjI ballI)
              apply (rule arg_cong[where f = Ector])
              apply (rule G.Sb_cong; (simp add: G.Vrs_Map)?)
              apply (metis EFVrs_def GVrs1 mem_Collect_eq)
             apply (metis Efree_alt(1) Efreee.GSupp1
            imsupp_empty_IntD2)
        subgoal for e a
          apply (cases "a \<in> GVrs2 u")
           apply (metis (mono_tags) IImsupp'_def Int_emptyD SSupp_def Un_iff mem_Collect_eq)
          apply (meson Efree\<eta>.GSupp1 Efree_alt(2))
          done
        subgoal for e a
          apply (cases "a \<in> GVrs2 u")
           apply (metis (mono_tags) IImsupp'_def Int_emptyD SSupp_def Un_iff mem_Collect_eq)
          apply (meson Efree\<eta>'.GSupp1 Efree_alt(3))
          done
          apply (meson Efree_alt(1) Efreee.GSupp2)
         apply (meson Efree\<eta>.simps Efree_alt(2))
        apply (meson Efree\<eta>'.simps Efree_alt(3))
        done
      done
    done
  done
unused_thms

end

end