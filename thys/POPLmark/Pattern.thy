theory Pattern
  imports POPLmark_1B
begin

datatype ('tvar::var, PPV: 'var) ppat = PPVr 'var "'tvar type" | PPRec "(label, ('tvar, 'var) ppat) lfset"

lemma finite_PPV: "finite (PPV P)"
  by (induct P) auto

definition nonrep_ppat :: "('tv::var, 'v::var) ppat \<Rightarrow> bool" where
  "nonrep_ppat P = (\<forall>Q :: ('tv, 'v) ppat. rel_ppat top P Q \<longrightarrow> (\<exists>f. Q = map_ppat f P))"

lemma nonrep_ppat_PPVar[simp]: "nonrep_ppat (PPVr x T)"
  unfolding nonrep_ppat_def
  apply safe
  subgoal for Q
    by (cases Q; auto)
  done

lemma PV_bd: "|PPV (x :: ('tv::var, 'v::var) ppat)| <o |UNIV :: 'v::var set|"
  by (rule ordLess_ordLeq_trans[OF ppat.set_bd]) (simp add: type_pre.var_large)

lemma values_lfupdate: "values (lfupdate X y x) \<subseteq> insert x (values X)"
  including lfset.lifting
  by transfer auto

lemma map_lfset_lfupdate: "map_lfset id f (lfupdate X y x) = lfupdate (map_lfset id f X) y (f x)"
  including lfset.lifting
  by transfer (auto 0 4 simp: image_iff map_prod_def split_beta)

lemma lfupdate_idle: "(y, Q) \<in>\<in> X \<Longrightarrow> X\<lbrace>y := Q\<rbrace> = X"
  including lfset.lifting
  by transfer (auto simp: nonrep_lfset_alt)

lemma lfin_lfupdate: "(x, Q) \<in>\<in> X\<lbrace>y := T\<rbrace> \<longleftrightarrow> (if x = y then Q = T else (x, Q) \<in>\<in> X)"
  including lfset.lifting
  by transfer auto

lemma map_ppat_idleD: "map_ppat f P = P \<Longrightarrow> z \<in> PPV P \<Longrightarrow> f z = z"
  apply (induct P)
   apply auto
  by (metis lfin_label_inject lfin_map_lfset values_lfin)

lemma map_ppat_swapD: "map_ppat f Q = map_ppat (id(z := z', z' := z)) Q \<Longrightarrow> z \<in> PPV Q \<Longrightarrow> f z = z'"
  apply (induct Q)
   apply auto
  by (metis (no_types, opaque_lifting) lfin_label_inject lfin_map_lfset values_lfin)

lemma nonrep_ppat_PRecD1: "nonrep_ppat (PPRec X :: ('tv::var, 'v::var) ppat) \<Longrightarrow> (x, P) \<in>\<in> X \<Longrightarrow>
  nonrep_ppat P"
  unfolding nonrep_ppat_def
  apply safe
  subgoal for Q
    apply (drule spec[where x="PPRec (X\<lbrace>x := Q\<rbrace>)"])
    apply (drule mp)
     apply (auto simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id]
      map_lfset_lfupdate lfset.set_map lfset.map_comp o_def lfset.map_ident ppat.rel_refl lfupdate_idle
      dest!: set_mp[OF values_lfupdate]
       intro!: exI[of _ "lfupdate (map_lfset id (\<lambda>P. (P, P)) X) x (P, Q)"]) []
    apply (erule exE)
    subgoal for f
      apply (rule exI[of _ f])
      apply (auto)
      by (metis lfin_lfupdate lfin_map_lfset)
    done
  done

lemma nonrep_ppat_PRecD2: "nonrep_ppat (PPRec X :: ('tv::var, 'v::var) ppat) \<Longrightarrow>
  (\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PPV P \<inter> PPV Q = {})"
proof (unfold nonrep_ppat_def, safe, goal_cases LR)
  case (LR x y P Q z)
  obtain z' where "z' \<notin> PPV (PPRec X)"
    using MRBNF_FP.exists_fresh[OF PV_bd] by blast
  with LR(4) have "rel_ppat top (PPRec X) (PPRec (lfupdate X y (map_ppat (id(z := z', z' := z)) Q)))"
    by (auto simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id]
      map_lfset_lfupdate lfset.map_comp o_def lfset.map_ident
      ppat.rel_map ppat.rel_refl lfset.set_map lfupdate_idle
      dest!: set_mp[OF values_lfupdate]
      intro!: exI[of _ "lfupdate (map_lfset id (\<lambda>P. (P, P)) X) y (Q, map_ppat (id(z := z', z' := z)) Q)"])
  with LR(1) obtain f where "map_ppat f (PPRec X) = PPRec (lfupdate X y (map_ppat (id(z := z', z' := z)) Q))"
    by metis
  then have *: "map_lfset id (map_ppat f) X = X\<lbrace>y := map_ppat (id(z := z', z' := z)) Q\<rbrace>"
    by (auto dest!: arg_cong[where f=PPV])
  then have "map_ppat f P = P"
    using LR(2) lfin_map_lfset[THEN iffD2, OF exI, OF conjI, OF _ LR(3), of "map_ppat f P" "map_ppat f"]
    by (auto simp: lfin_lfupdate lfin_label_inject LR(3))
  then have "f z = z"
    using LR(5) map_ppat_idleD by metis
  moreover from * have "map_ppat f Q = map_ppat (id(z := z', z' := z)) Q"
    using lfin_map_lfset[THEN iffD2, OF exI, OF conjI, OF _ LR(4), of "map_ppat f Q" "map_ppat f"]
    by (auto simp: lfin_lfupdate)
  then have "f z = z'"
    using LR(6) map_ppat_swapD by metis
  ultimately show ?case
    by (metis LR(3,5) \<open>z' \<notin> PPV (PPRec X)\<close> lfin_values ppat.set_intros(2))
qed

lemma lfset_eq_iff: "X = Y \<longleftrightarrow> (\<forall>x P. (x, P) \<in>\<in> X \<longleftrightarrow> (x, P) \<in>\<in> Y)"
  including lfset.lifting
  by transfer auto

lemma nonrep_ppat_PRecI:
  assumes
    "(\<forall>x P. (x, P) \<in>\<in> X \<longrightarrow> nonrep_ppat P)"
    "(\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PPV P \<inter> PPV Q = {})"
  shows "nonrep_ppat (PPRec X :: ('tv::var, 'v::var) ppat)"
  using assms
  unfolding nonrep_ppat_def
proof (safe, goal_cases RL)
  case (RL QQ)
  then obtain Y where "QQ = PPRec Y"
    by (cases QQ; simp)
  with RL(3) have *: "rel_lfset id (rel_ppat top) X Y" by auto
  { fix x P
    assume xP: "(x, P) \<in>\<in> X"
    with * obtain Q where "(x, Q) \<in>\<in> Y" "rel_ppat top P Q"
      including lfset.lifting
      by (atomize_elim, transfer) (force simp: rel_fset_alt)
    moreover
    from assms(1) xP \<open>rel_ppat top P Q\<close> obtain f where "map_ppat f P = Q"
      unfolding nonrep_ppat_def by blast
    then obtain g where "supp g \<subseteq> PPV P" "map_ppat g P = Q"
      by (atomize_elim, intro exI[of _ "\<lambda>x. if x \<in> PPV P then f x else x"])
        (auto simp: supp_def intro: ppat.map_cong)
    ultimately have "\<exists>f. (x, map_ppat f P) \<in>\<in> Y \<and> supp f \<subseteq> PPV P"
      by auto
  } note pick_ex = this
  define pick where "pick = (\<lambda>x (P :: ('tv::var, 'v::var) ppat). SOME f. (x, map_ppat f P) \<in>\<in> Y \<and> supp f \<subseteq> PPV P)"
  have pick: "(x, map_ppat (pick x P) P) \<in>\<in> Y" "supp (pick x P) \<subseteq> PPV P" if "(x, P) \<in>\<in> X" for x P
    using someI_ex[OF pick_ex[OF that]] unfolding pick_def
    by (auto simp: Eps_case_prod)
  define pick_part where "pick_part = (\<lambda>z. THE (x, P). (x, P) \<in>\<in> X \<and> z \<in> PPV P)"
  have pick_part: "pick_part z \<in>\<in> X \<and> z \<in> PPV (snd (pick_part z))" if "\<exists>x P. (x, P) \<in>\<in> X \<and> z \<in> PPV P" for z
    using that assms(2) unfolding pick_part_def
    apply -
    apply (rule the1I2)
     apply auto
     apply blast
    by (metis Int_emptyD lfin_label_inject)
  define pick1 where "pick1 = (\<lambda>z. if \<exists>x P. (x, P) \<in>\<in> X \<and> z \<in> PPV P then case_prod pick (pick_part z) z else z)"
  show ?case
    unfolding \<open>QQ = PPRec Y\<close>
    apply (auto intro!: exI[of _ pick1] simp: pick1_def lfset_eq_iff lfin_map_lfset)
    subgoal for x P
      apply (subgoal_tac "\<exists>P'. (x, P') \<in>\<in> X \<and> rel_ppat top P' P")
       apply auto
       apply (frule pick)
      subgoal for P'
        apply (rule exI[of _ P'])
        apply auto
        apply (rule sym)
        apply (rule trans[OF ppat.map_cong[OF refl]])
         apply (rule if_P)
         apply (auto simp: split_beta)
        apply (rule trans[OF ppat.map_cong[OF refl], of _ _ "pick x P'"])
        apply (metis Int_emptyD assms(2) lfin_label_inject pick_part surjective_pairing)
        apply (simp add: lfin_label_inject)
        done
      subgoal
        using *
        including lfset.lifting
        by transfer (force simp: rel_fset_alt)
      done
    subgoal for x P
      apply (frule pick)
      using
        \<open>\<And>x P. (x, P) \<in>\<in> Y \<Longrightarrow> \<exists>c. P = map_ppat (\<lambda>z. if \<exists>x P. (x, P) \<in>\<in> X \<and> z \<in> PPV P then (case pick_part z of (x, xa) \<Rightarrow> pick x xa) z else z) c \<and> (x, c) \<in>\<in> X\<close>
        lfin_label_inject by fastforce
    done
qed

definition "nonrep_PPRec X = (\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PPV P \<inter> PPV Q = {})"

lemma nonrep_PPRec_lfemtpy[simp]: "nonrep_PPRec lfempty"
  unfolding nonrep_PPRec_def by auto

lemma nonrep_ppat_PRec[simp]: "nonrep_ppat (PPRec X :: ('tv::var, 'v::var) ppat) \<longleftrightarrow>
  ((\<forall>x P. (x, P) \<in>\<in> X \<longrightarrow> nonrep_ppat P) \<and>
  nonrep_PPRec X)"
  unfolding nonrep_PPRec_def
  using nonrep_ppat_PRecI[of X] nonrep_ppat_PRecD1[of X] nonrep_ppat_PRecD2[of X] by blast

typedef ('tv::var, 'v::var) pat = "{p :: ('tv, 'v) ppat. nonrep_ppat p}"
  by (auto intro!: exI[of _ "PPVr undefined undefined"])

setup_lifting type_definition_pat

lift_definition PVr :: "'v \<Rightarrow> 'tv type \<Rightarrow> ('tv::var, 'v::var) pat" is PPVr
  by auto

lemma PVar_inject[simp]: "PVr X T = PVr Y U \<longleftrightarrow> X = Y \<and> T = U"
  by transfer auto

definition PRec :: "(label, ('tv::var, 'v::var) pat) lfset \<Rightarrow> ('tv::var, 'v::var) pat" where
  "PRec X = (if nonrep_PPRec (map_lfset id Rep_pat X) then Abs_pat (PPRec (map_lfset id Rep_pat X)) else Abs_pat (PPRec lfempty))"

lemma PRec_transfer[transfer_rule]: "rel_fun (rel_lfset id cr_pat) cr_pat (\<lambda>X. if nonrep_PPRec X then PPRec X else PPRec lfempty) PRec"
  apply (auto simp: PRec_def rel_fun_def cr_pat_def lfset.map_comp Abs_pat_inverse
    lfset.in_rel[of id, simplified, unfolded lfset.map_id])
  apply (subst Abs_pat_inverse)
     apply (auto simp: Abs_pat_inverse lfin_map_lfset Rep_pat Collect_prod_beta subset_eq
       intro!: lfset.map_cong)
  using Rep_pat apply blast
  apply (simp_all add: lfset.map_cong_id)
  done

fun vvsubst_ppat where
  "vvsubst_ppat \<tau> \<sigma> (PPVr v T) = PPVr (\<sigma> v) (vvsubst_type \<tau> T)"
| "vvsubst_ppat \<tau> \<sigma> (PPRec X) = PPRec (map_lfset id (vvsubst_ppat \<tau> \<sigma>) X)"

fun subst_ppat where
  "subst_ppat \<tau> \<sigma> (PPVr v T) = PPVr (\<sigma> v) (substT \<tau> T)"
| "subst_ppat \<tau> \<sigma> (PPRec X) = PPRec (map_lfset id (subst_ppat \<tau> \<sigma>) X)"

fun PPTV where
  "PPTV (PPVr v T) = TFV T"
| "PPTV (PPRec X) = (\<Union>P \<in> values X. PPTV P)"

lemma finite_PPTV: "finite (PPTV P)"
  by (induct P) auto

lemma PPV_vvsubst_ppat[simp]: "PPV (vvsubst_ppat \<tau> \<sigma> P) = \<sigma> ` PPV P"
  by (induct P) (auto simp: lfset.set_map)

lemma PPV_subst_ppat[simp]: "PPV (subst_ppat \<tau> \<sigma> P) = \<sigma> ` PPV P"
  by (induct P) (auto simp: lfset.set_map)

lemma PPTV_vvsubst_ppat[simp]:
  fixes P :: "('tv::var, 'v::var) ppat"
  shows "|supp \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> PPTV (vvsubst_ppat \<tau> \<sigma> P) = \<tau> ` PPTV P"
  by (induct P) (auto simp: lfset.set_map type.set_map)

lemma PPTV_subst_ppat[simp]: 
  fixes P :: "('tv::var, 'v::var) ppat"
  shows "|SSupp_type \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> PPTV (subst_ppat \<tau> \<sigma> P) = (\<Union>x \<in> PPTV P. TFV (\<tau> x))"
  by (induct P) (auto simp: lfset.set_map FVars_substT)

lemma nonrep_ppat_vvsubst_ppat:
  "bij \<sigma> \<Longrightarrow> nonrep_ppat P \<Longrightarrow> nonrep_ppat (vvsubst_ppat \<tau> \<sigma> P)"
  apply (induct P)
   apply (auto simp: lfin_map_lfset lfin_values nonrep_PPRec_def)
  apply (metis Int_emptyD bij_implies_inject)
  done

lift_definition vvsubst_pat :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('tv::var, 'v::var) pat \<Rightarrow> ('tv::var, 'v::var) pat" is
  "\<lambda>\<tau> \<sigma>. if bij \<sigma> then vvsubst_ppat \<tau> \<sigma> else id"
  by (auto simp: nonrep_ppat_vvsubst_ppat)

lemma nonrep_ppat_subst_ppat:
  "bij \<sigma> \<Longrightarrow> nonrep_ppat P \<Longrightarrow> nonrep_ppat (subst_ppat \<tau> \<sigma> P)"
  apply (induct P)
   apply (auto simp: lfin_map_lfset lfin_values nonrep_PPRec_def)
  apply (metis Int_emptyD bij_implies_inject)
  done

lift_definition subst_pat :: "('tv \<Rightarrow> 'tv type) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('tv::var, 'v::var) pat \<Rightarrow> ('tv::var, 'v::var) pat" is
  "\<lambda>\<tau> \<sigma>. if bij \<sigma> then subst_ppat \<tau> \<sigma> else id"
  by (auto simp: nonrep_ppat_subst_ppat)

lift_definition PV :: "('tv::var, 'v::var) pat \<Rightarrow> 'v set" is
  "PPV" .

lift_definition PTV :: "('tv::var, 'v::var) pat \<Rightarrow> 'tv set" is
  "PPTV" .

lemma PV_vvsubst_pat: "bij \<sigma> \<Longrightarrow> PV (vvsubst_pat \<tau> \<sigma> P) = \<sigma> ` PV P"
  by transfer auto

lemma PV_subst_pat: "bij \<sigma> \<Longrightarrow> PV (subst_pat \<tau> \<sigma> P) = \<sigma> ` PV P"
  by transfer auto

lemma PTV_vvsubst_pat:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|supp \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> bij \<sigma> \<Longrightarrow> PTV (vvsubst_pat \<tau> \<sigma> P) = \<tau> ` PTV P"
  by transfer auto

lemma PTV_subst_pat:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|SSupp_type \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> bij \<sigma> \<Longrightarrow> PTV (subst_pat \<tau> \<sigma> P) = (\<Union>x \<in> PTV P. TFV (\<tau> x))"
  by transfer auto

lemma vvsubst_ppat_subst_ppat:
  fixes P :: "('tv::var, 'v::var) ppat"
  shows "|supp \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow>
    vvsubst_ppat \<tau> \<sigma> P = subst_ppat (TVr o \<tau>) \<sigma> P"
  by (induct P) (auto simp: vvsubst_type_substT intro!: lfset.map_cong)

lemma vvsubst_pat_subst_pat:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|supp \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow>
    vvsubst_pat \<tau> \<sigma> P = subst_pat (TVr o \<tau>) \<sigma> P"
  by transfer (auto simp: vvsubst_ppat_subst_ppat)

lemma subst_ppat_comp:
  fixes P :: "('tv::var, 'v::var) ppat"
  shows "|SSupp_type \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> |SSupp_type \<tau>'| <o |UNIV :: 'tv::var set| \<Longrightarrow>
    subst_ppat \<tau> \<sigma> (subst_ppat \<tau>' \<sigma>' P) = subst_ppat (substT \<tau> o \<tau>') (\<sigma> o \<sigma>') P"
  by (induct P) (auto simp: substT_comp lfset.map_comp intro!: lfset.map_cong)

lemma subst_ppat_cong:
  fixes P :: "('tv::var, 'v::var) ppat"
  shows "|SSupp_type \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> |SSupp_type \<tau>'| <o |UNIV :: 'tv::var set| \<Longrightarrow>
  (\<forall>x \<in> PPTV P. \<tau> x = \<tau>' x) \<Longrightarrow> (\<forall>x \<in> PPV P. \<sigma> x = \<sigma>' x) \<Longrightarrow>  
  subst_ppat \<tau> \<sigma> P = subst_ppat \<tau>' \<sigma>' P"
  by (induct P) (auto intro!: lfset.map_cong substT_cong)

lemma subst_pat_comp:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|SSupp_type \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> |SSupp_type \<tau>'| <o |UNIV :: 'tv::var set| \<Longrightarrow> bij \<sigma> \<Longrightarrow> bij \<sigma>' \<Longrightarrow>
    subst_pat \<tau> \<sigma> (subst_pat \<tau>' \<sigma>' P) = subst_pat (substT \<tau> o \<tau>') (\<sigma> o \<sigma>') P"
  by transfer (auto simp: subst_ppat_comp)

lemma subst_pat_cong:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|SSupp_type \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> |SSupp_type \<tau>'| <o |UNIV :: 'tv::var set| \<Longrightarrow> bij \<sigma> \<Longrightarrow> bij \<sigma>' \<Longrightarrow>
  (\<forall>x \<in> PTV P. \<tau> x = \<tau>' x) \<Longrightarrow> (\<forall>x \<in> PV P. \<sigma> x = \<sigma>' x) \<Longrightarrow>  
  subst_pat \<tau> \<sigma> P = subst_pat \<tau>' \<sigma>' P"
  by transfer (auto simp: subst_ppat_cong)

lemma vvsubst_pat_id[simp]: "vvsubst_pat id id P = P"
  apply transfer
  subgoal for P
    apply (induct P)
     apply (force simp: type.map_id values_lfin_iff intro!: trans[OF lfset.map_cong_id lfset.map_id])+
    done
  done

mrbnf "('tv :: var, 'v :: var) pat"
  map: vvsubst_pat
  sets:
    free: PTV
    bound: "PV"
  bd: "natLeq"
  rel: "(=)"
  subgoal
    apply (rule ext)
    apply simp
    done
  subgoal for f1 f2 g1 g2
    apply (rule ext)
    apply (transfer fixing: f1 f2 g1 g2)
    subgoal for P
      apply (induct P)
       apply (force simp: type.map_comp lfset.map_comp values_lfin_iff intro!: lfset.map_cong)+
      done
    done
  subgoal for P f1 f2 g1 g2
    apply (transfer fixing: f1 f2 g1 g2)
    subgoal for P
      apply (induct P)
       apply (fastforce simp: values_lfin_iff Bex_def intro!: type.map_cong lfset.map_cong)+
      done
    done
  subgoal for f g
    apply (rule ext)
    apply (transfer fixing: f g)
    subgoal for P
      apply (induct P)
       apply (fastforce simp: type.set_map lfset.set_map values_lfin_iff)+
      done
    done
  subgoal for f g
    apply (rule ext)
    apply (transfer fixing: f g)
    subgoal for P
      apply (induct P)
       apply (fastforce simp: type.set_map lfset.set_map values_lfin_iff)+
      done
    done
  subgoal by (simp add: infinite_regular_card_order_natLeq)
  subgoal for P
    apply transfer
    subgoal for P
    apply (induct P)
       apply (force simp: type.FVars_bd lfset.set_bd values_lfin_iff intro!: stable_UNION[OF stable_natLeq])+
      done
    done
  subgoal for P
    apply transfer
    subgoal for P
    apply (induct P)
       apply (force simp: type.FVars_bd lfset.set_bd ID.set_bd values_lfin_iff intro!: stable_UNION[OF stable_natLeq])+
      done
    done
  subgoal by simp
  subgoal by simp
  done

lemma vvsubst_pat_PVar[simp]:
  "bij g \<Longrightarrow> vvsubst_pat f g (PVr x T) = PVr (g x) (vvsubst_type f T)"
  by transfer auto
lemma subst_pat_PVar[simp]:
  "bij g \<Longrightarrow> subst_pat f g (PVr x T) = PVr (g x) (substT f T)"
  by transfer auto

definition "nonrep_PRec X = (\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PV P \<inter> PV Q = {})"

lemma nonrep_PRec_alt: "nonrep_PRec X = nonrep_PPRec (map_lfset id Rep_pat X)"
  unfolding nonrep_PRec_def nonrep_PPRec_def
  apply (auto simp: PV_def)
   apply (metis Int_emptyD lfin_map_lfset)
  apply (meson Int_emptyD lfin_map_lfset)
  done

lemma PRec_inject[simp]: "nonrep_PRec PP \<Longrightarrow> nonrep_PRec UU \<Longrightarrow> PRec PP = PRec UU \<longleftrightarrow> PP = UU"
  unfolding PRec_def
  apply (auto simp: nonrep_PRec_alt)
  apply (subst (asm) Abs_pat_inject)
    apply (auto simp: Rep_pat_inject elim!: lfset.inj_map_strong[rotated])
  apply (metis Rep_pat lfin_map_lfset mem_Collect_eq)
  apply (metis Rep_pat lfin_map_lfset mem_Collect_eq)
  done

lemma vvsubst_pat_PRec[simp]:
  "bij g \<Longrightarrow> nonrep_PRec P \<Longrightarrow> vvsubst_pat f g (PRec P) = PRec (map_lfset id (vvsubst_pat f g) P)"
  unfolding PRec_def vvsubst_pat_def nonrep_PRec_alt
  apply (auto simp: lfset.map_comp o_def map_fun_def id_def[symmetric])
     apply (subst (1 2) Abs_pat_inverse)
  using Rep_pat nonrep_ppat_vvsubst_ppat apply blast
  apply (auto) []
      apply (metis Rep_pat lfin_map_lfset mem_Collect_eq)
     apply (subst Abs_pat_inject)
  apply (metis (mono_tags, lifting) Rep_pat lfin_map_lfset mem_Collect_eq nonrep_ppat_PRec
      nonrep_ppat_vvsubst_ppat)
  apply (smt (verit, best) Abs_pat_inverse Rep_pat lfin_map_lfset lfset.map_cong_id
      mem_Collect_eq nonrep_ppat_PRec nonrep_ppat_vvsubst_ppat)
     apply (auto simp: lfset.map_comp intro!: lfset.map_cong) []
  apply (smt (z3) Abs_pat_inverse Rep_pat lfin_map_lfset mem_Collect_eq nonrep_PPRec_def
      nonrep_ppat_PRec nonrep_ppat_vvsubst_ppat
      vvsubst_ppat.simps(2))
  done

lemma subst_pat_PRec[simp]:
  "bij g \<Longrightarrow> nonrep_PRec P \<Longrightarrow> subst_pat f g (PRec P) = PRec (map_lfset id (subst_pat f g) P)"
  unfolding PRec_def subst_pat_def nonrep_PRec_alt
  apply (auto simp: lfset.map_comp o_def map_fun_def id_def[symmetric])
     apply (subst (1 2) Abs_pat_inverse)
  using Rep_pat nonrep_ppat_subst_ppat apply blast
  apply (auto) []
      apply (metis Rep_pat lfin_map_lfset mem_Collect_eq)
     apply (subst Abs_pat_inject)
  apply (metis (mono_tags, lifting) Rep_pat lfin_map_lfset mem_Collect_eq nonrep_ppat_PRec
      nonrep_ppat_subst_ppat)
  apply (smt (verit, best) Abs_pat_inverse Rep_pat lfin_map_lfset lfset.map_cong_id
      mem_Collect_eq nonrep_ppat_PRec nonrep_ppat_subst_ppat)
     apply (auto simp: lfset.map_comp intro!: lfset.map_cong) []
  apply (smt (z3) Abs_pat_inverse Rep_pat lfin_map_lfset mem_Collect_eq nonrep_PPRec_def
      nonrep_ppat_PRec nonrep_ppat_subst_ppat
      subst_ppat.simps(2))
  done

lemma PV_PVar[simp]: "PV (PVr x T) = {x}"
  by (auto simp: PV_def PVr_def Abs_pat_inverse)
lemma PV_PRec[simp]: "nonrep_PRec P \<Longrightarrow> PV (PRec P) = (\<Union>x \<in> values P. PV x)"
  apply (auto simp: PV_def PRec_def Abs_pat_inverse nonrep_PRec_alt lfin_map_lfset lfset.set_map Rep_pat[simplified])
   apply (subst (asm) Abs_pat_inverse; auto simp: lfin_map_lfset Rep_pat[simplified] lfset.set_map)
   apply (subst Abs_pat_inverse; auto simp: lfin_map_lfset Rep_pat[simplified] lfset.set_map)
  done
lemma PTV_PVar[simp]: "PTV (PVr x T) = TFV T"
  by (auto simp: PTV_def PVr_def Abs_pat_inverse)
lemma PTV_PRec[simp]: "nonrep_PRec P \<Longrightarrow> PTV (PRec P) = (\<Union>x \<in> values P. PTV x)"
  apply (auto simp: PTV_def PRec_def Abs_pat_inverse nonrep_PRec_alt lfin_map_lfset lfset.set_map Rep_pat[simplified])
   apply (subst (asm) Abs_pat_inverse; auto simp: lfin_map_lfset Rep_pat[simplified] lfset.set_map)
   apply (subst Abs_pat_inverse; auto simp: lfin_map_lfset Rep_pat[simplified] lfset.set_map)
  done

lemma finite_PV[simp]: "finite (PV P)"
  by (auto simp: PV_def finite_PPV)
lemma finite_PTV[simp]: "finite (PTV P)"
  by (auto simp: PTV_def finite_PPTV)

end