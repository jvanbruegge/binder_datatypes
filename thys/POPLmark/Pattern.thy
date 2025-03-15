theory Pattern
  imports POPLmark_1B
begin

datatype ('tv::var, PPVars: 'v) rawpat = PPVar 'v "'tv typ" | PPRec "(label, ('tv, 'v) rawpat) lfset"

definition nonrep_rawpat :: "('tv::var, 'v::var) rawpat \<Rightarrow> bool" where
  "nonrep_rawpat P = (\<forall>Q :: ('tv, 'v) rawpat. rel_rawpat top P Q \<longrightarrow> (\<exists>f. Q = map_rawpat f P))"

lemma nonrep_rawpat_PPVar[simp]: "nonrep_rawpat (PPVar x T)"
  unfolding nonrep_rawpat_def
  apply safe
  subgoal for Q
    by (cases Q; auto)
  done

lemma PVars_bd: "|PPVars (x :: ('tv::var, 'v::var) rawpat)| <o |UNIV :: 'v::var set|"
  by (rule ordLess_ordLeq_trans[OF rawpat.set_bd]) (simp add: typ_pre.var_large)

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

lemma map_rawpat_idleD: "map_rawpat f P = P \<Longrightarrow> z \<in> PPVars P \<Longrightarrow> f z = z"
  apply (induct P)
   apply auto
  by (metis lfin_label_inject lfin_map_lfset values_lfin)

lemma map_rawpat_swapD: "map_rawpat f Q = map_rawpat (id(z := z', z' := z)) Q \<Longrightarrow> z \<in> PPVars Q \<Longrightarrow> f z = z'"
  apply (induct Q)
   apply auto
  by (metis (no_types, opaque_lifting) lfin_label_inject lfin_map_lfset values_lfin)

lemma nonrep_rawpat_PRecD1: "nonrep_rawpat (PPRec X :: ('tv::var, 'v::var) rawpat) \<Longrightarrow> (x, P) \<in>\<in> X \<Longrightarrow>
  nonrep_rawpat P"
  unfolding nonrep_rawpat_def
  apply safe
  subgoal for Q
    apply (drule spec[where x="PPRec (X\<lbrace>x := Q\<rbrace>)"])
    apply (drule mp)
     apply (auto simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id]
      map_lfset_lfupdate lfset.set_map lfset.map_comp o_def lfset.map_ident rawpat.rel_refl lfupdate_idle
      dest!: set_mp[OF values_lfupdate]
       intro!: exI[of _ "lfupdate (map_lfset id (\<lambda>P. (P, P)) X) x (P, Q)"]) []
    apply (erule exE)
    subgoal for f
      apply (rule exI[of _ f])
      apply (auto)
      by (metis lfin_lfupdate lfin_map_lfset)
    done
  done

lemma nonrep_rawpat_PRecD2: "nonrep_rawpat (PPRec X :: ('tv::var, 'v::var) rawpat) \<Longrightarrow>
  (\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PPVars P \<inter> PPVars Q = {})"
proof (unfold nonrep_rawpat_def, safe, goal_cases LR)
  case (LR x y P Q z)
  obtain z' where "z' \<notin> PPVars (PPRec X)"
    using MRBNF_FP.exists_fresh[OF PVars_bd] by blast
  with LR(4) have "rel_rawpat top (PPRec X) (PPRec (lfupdate X y (map_rawpat (id(z := z', z' := z)) Q)))"
    by (auto simp: lfset.in_rel[of id, simplified, unfolded lfset.map_id]
      map_lfset_lfupdate lfset.map_comp o_def lfset.map_ident
      rawpat.rel_map rawpat.rel_refl lfset.set_map lfupdate_idle
      dest!: set_mp[OF values_lfupdate]
      intro!: exI[of _ "lfupdate (map_lfset id (\<lambda>P. (P, P)) X) y (Q, map_rawpat (id(z := z', z' := z)) Q)"])
  with LR(1) obtain f where "map_rawpat f (PPRec X) = PPRec (lfupdate X y (map_rawpat (id(z := z', z' := z)) Q))"
    by metis
  then have *: "map_lfset id (map_rawpat f) X = X\<lbrace>y := map_rawpat (id(z := z', z' := z)) Q\<rbrace>"
    by (auto dest!: arg_cong[where f=PPVars])
  then have "map_rawpat f P = P"
    using LR(2) lfin_map_lfset[THEN iffD2, OF exI, OF conjI, OF _ LR(3), of "map_rawpat f P" "map_rawpat f"]
    by (auto simp: lfin_lfupdate lfin_label_inject LR(3))
  then have "f z = z"
    using LR(5) map_rawpat_idleD by metis
  moreover from * have "map_rawpat f Q = map_rawpat (id(z := z', z' := z)) Q"
    using lfin_map_lfset[THEN iffD2, OF exI, OF conjI, OF _ LR(4), of "map_rawpat f Q" "map_rawpat f"]
    by (auto simp: lfin_lfupdate)
  then have "f z = z'"
    using LR(6) map_rawpat_swapD by metis
  ultimately show ?case
    by (metis LR(3,5) \<open>z' \<notin> PPVars (PPRec X)\<close> lfin_values rawpat.set_intros(2))
qed

lemma lfset_eq_iff: "X = Y \<longleftrightarrow> (\<forall>x P. (x, P) \<in>\<in> X \<longleftrightarrow> (x, P) \<in>\<in> Y)"
  including lfset.lifting
  by transfer auto

lemma nonrep_rawpat_PRecI:
  assumes
    "(\<forall>x P. (x, P) \<in>\<in> X \<longrightarrow> nonrep_rawpat P)"
    "(\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PPVars P \<inter> PPVars Q = {})"
  shows "nonrep_rawpat (PPRec X :: ('tv::var, 'v::var) rawpat)"
  using assms
  unfolding nonrep_rawpat_def
proof (safe, goal_cases RL)
  case (RL QQ)
  then obtain Y where "QQ = PPRec Y"
    by (cases QQ; simp)
  with RL(3) have *: "rel_lfset id (rel_rawpat top) X Y" by auto
  { fix x P
    assume xP: "(x, P) \<in>\<in> X"
    with * obtain Q where "(x, Q) \<in>\<in> Y" "rel_rawpat top P Q"
      including lfset.lifting
      by (atomize_elim, transfer) (force simp: rel_fset_alt)
    moreover
    from assms(1) xP \<open>rel_rawpat top P Q\<close> obtain f where "map_rawpat f P = Q"
      unfolding nonrep_rawpat_def by blast
    then obtain g where "supp g \<subseteq> PPVars P" "map_rawpat g P = Q"
      by (atomize_elim, intro exI[of _ "\<lambda>x. if x \<in> PPVars P then f x else x"])
        (auto simp: supp_def intro: rawpat.map_cong)
    ultimately have "\<exists>f. (x, map_rawpat f P) \<in>\<in> Y \<and> supp f \<subseteq> PPVars P"
      by auto
  } note pick_ex = this
  define pick where "pick = (\<lambda>x (P :: ('tv::var, 'v::var) rawpat). SOME f. (x, map_rawpat f P) \<in>\<in> Y \<and> supp f \<subseteq> PPVars P)"
  have pick: "(x, map_rawpat (pick x P) P) \<in>\<in> Y" "supp (pick x P) \<subseteq> PPVars P" if "(x, P) \<in>\<in> X" for x P
    using someI_ex[OF pick_ex[OF that]] unfolding pick_def
    by (auto simp: Eps_case_prod)
  define pick_part where "pick_part = (\<lambda>z. THE (x, P). (x, P) \<in>\<in> X \<and> z \<in> PPVars P)"
  have pick_part: "pick_part z \<in>\<in> X \<and> z \<in> PPVars (snd (pick_part z))" if "\<exists>x P. (x, P) \<in>\<in> X \<and> z \<in> PPVars P" for z
    using that assms(2) unfolding pick_part_def
    apply -
    apply (rule the1I2)
     apply auto
     apply blast
    by (metis Int_emptyD lfin_label_inject)
  define pick1 where "pick1 = (\<lambda>z. if \<exists>x P. (x, P) \<in>\<in> X \<and> z \<in> PPVars P then case_prod pick (pick_part z) z else z)"
  show ?case
    unfolding \<open>QQ = PPRec Y\<close>
    apply (auto intro!: exI[of _ pick1] simp: pick1_def lfset_eq_iff lfin_map_lfset)
    subgoal for x P
      apply (subgoal_tac "\<exists>P'. (x, P') \<in>\<in> X \<and> rel_rawpat top P' P")
       apply auto
       apply (frule pick)
      subgoal for P'
        apply (rule exI[of _ P'])
        apply auto
        apply (rule sym)
        apply (rule trans[OF rawpat.map_cong[OF refl]])
         apply (rule if_P)
         apply (auto simp: split_beta)
        apply (rule trans[OF rawpat.map_cong[OF refl], of _ _ "pick x P'"])
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
        \<open>\<And>x P. (x, P) \<in>\<in> Y \<Longrightarrow> \<exists>c. P = map_rawpat (\<lambda>z. if \<exists>x P. (x, P) \<in>\<in> X \<and> z \<in> PPVars P then (case pick_part z of (x, xa) \<Rightarrow> pick x xa) z else z) c \<and> (x, c) \<in>\<in> X\<close>
        lfin_label_inject by fastforce
    done
qed

definition "nonrep_PPRec X = (\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PPVars P \<inter> PPVars Q = {})"

lemma nonrep_PPRec_lfemtpy[simp]: "nonrep_PPRec lfempty"
  unfolding nonrep_PPRec_def by auto

lemma nonrep_rawpat_PRec[simp]: "nonrep_rawpat (PPRec X :: ('tv::var, 'v::var) rawpat) \<longleftrightarrow>
  ((\<forall>x P. (x, P) \<in>\<in> X \<longrightarrow> nonrep_rawpat P) \<and>
  nonrep_PPRec X)"
  unfolding nonrep_PPRec_def
  using nonrep_rawpat_PRecI[of X] nonrep_rawpat_PRecD1[of X] nonrep_rawpat_PRecD2[of X] by blast

typedef ('tv::var, 'v::var) pat = "{p :: ('tv, 'v) rawpat. nonrep_rawpat p}"
  by (auto intro!: exI[of _ "PPVar undefined undefined"])

setup_lifting type_definition_pat

lift_definition PVar :: "'v \<Rightarrow> 'tv typ \<Rightarrow> ('tv::var, 'v::var) pat" is PPVar
  by auto

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

fun vvsubst_rawpat where
  "vvsubst_rawpat \<tau> \<sigma> (PPVar v T) = PPVar (\<sigma> v) (vvsubst_typ \<tau> T)"
| "vvsubst_rawpat \<tau> \<sigma> (PPRec X) = PPRec (map_lfset id (vvsubst_rawpat \<tau> \<sigma>) X)"

fun tvsubst_rawpat where
  "tvsubst_rawpat \<tau> \<sigma> (PPVar v T) = PPVar (\<sigma> v) (tvsubst_typ \<tau> T)"
| "tvsubst_rawpat \<tau> \<sigma> (PPRec X) = PPRec (map_lfset id (tvsubst_rawpat \<tau> \<sigma>) X)"

fun PPTVars where
  "PPTVars (PPVar v T) = FVars_typ T"
| "PPTVars (PPRec X) = (\<Union>P \<in> values X. PPTVars P)"

lemma PPVars_vvsubst_rawpat[simp]: "PPVars (vvsubst_rawpat \<tau> \<sigma> P) = \<sigma> ` PPVars P"
  by (induct P) (auto simp: lfset.set_map)

lemma PPVars_tvsubst_rawpat[simp]: "PPVars (tvsubst_rawpat \<tau> \<sigma> P) = \<sigma> ` PPVars P"
  by (induct P) (auto simp: lfset.set_map)

lemma PPTVars_vvsubst_rawpat[simp]:
  fixes P :: "('tv::var, 'v::var) rawpat"
  shows "|supp \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> PPTVars (vvsubst_rawpat \<tau> \<sigma> P) = \<tau> ` PPTVars P"
  by (induct P) (auto simp: lfset.set_map typ.set_map)

lemma PPTVars_tvsubst_rawpat[simp]: 
  fixes P :: "('tv::var, 'v::var) rawpat"
  shows "|SSupp_typ \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> PPTVars (tvsubst_rawpat \<tau> \<sigma> P) = (\<Union>x \<in> PPTVars P. FVars_typ (\<tau> x))"
  by (induct P) (auto simp: lfset.set_map FVars_tvsubst_typ)

lemma nonrep_rawpat_vvsubst_rawpat:
  "bij \<sigma> \<Longrightarrow> nonrep_rawpat P \<Longrightarrow> nonrep_rawpat (vvsubst_rawpat \<tau> \<sigma> P)"
  apply (induct P)
   apply (auto simp: lfin_map_lfset lfin_values nonrep_PPRec_def)
  apply (metis Int_emptyD bij_implies_inject)
  done

lift_definition vvsubst_pat :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('tv::var, 'v::var) pat \<Rightarrow> ('tv::var, 'v::var) pat" is
  "\<lambda>\<tau> \<sigma>. if bij \<sigma> then vvsubst_rawpat \<tau> \<sigma> else id"
  by (auto simp: nonrep_rawpat_vvsubst_rawpat)

lemma nonrep_rawpat_tvsubst_rawpat:
  "bij \<sigma> \<Longrightarrow> nonrep_rawpat P \<Longrightarrow> nonrep_rawpat (tvsubst_rawpat \<tau> \<sigma> P)"
  apply (induct P)
   apply (auto simp: lfin_map_lfset lfin_values nonrep_PPRec_def)
  apply (metis Int_emptyD bij_implies_inject)
  done

lift_definition tvsubst_pat :: "('tv \<Rightarrow> 'tv typ) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('tv::var, 'v::var) pat \<Rightarrow> ('tv::var, 'v::var) pat" is
  "\<lambda>\<tau> \<sigma>. if bij \<sigma> then tvsubst_rawpat \<tau> \<sigma> else id"
  by (auto simp: nonrep_rawpat_tvsubst_rawpat)

lift_definition PVars :: "('tv::var, 'v::var) pat \<Rightarrow> 'v set" is
  "PPVars" .

lift_definition PTVars :: "('tv::var, 'v::var) pat \<Rightarrow> 'tv set" is
  "PPTVars" .

lemma values_lfin_iff: "c \<in> values x \<longleftrightarrow> (\<exists>l. (l, c) \<in>\<in> x)"
  including lfset.lifting
  by transfer force

lemma PVars_tvsubst_pat: "bij \<sigma> \<Longrightarrow> PVars (tvsubst_pat \<tau> \<sigma> P) = \<sigma> ` PVars P"
  by transfer auto

lemma PTVars_tvsubst_pat:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|SSupp_typ \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> bij \<sigma> \<Longrightarrow> PTVars (tvsubst_pat \<tau> \<sigma> P) = (\<Union>x \<in> PTVars P. FVars_typ (\<tau> x))"
  by transfer auto

lemma vvsubst_rawpat_tvsubst_rawpat:
  fixes P :: "('tv::var, 'v::var) rawpat"
  shows "|supp \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow>
    vvsubst_rawpat \<tau> \<sigma> P = tvsubst_rawpat (TyVar o \<tau>) \<sigma> P"
  by (induct P) (auto simp: vvsubst_typ_tvsubst_typ intro!: lfset.map_cong)

lemma vvsubst_pat_tvsubst_pat:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|supp \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow>
    vvsubst_pat \<tau> \<sigma> P = tvsubst_pat (TyVar o \<tau>) \<sigma> P"
  by transfer (auto simp: vvsubst_rawpat_tvsubst_rawpat)

lemma tvsubst_rawpat_comp:
  fixes P :: "('tv::var, 'v::var) rawpat"
  shows "|SSupp_typ \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> |SSupp_typ \<tau>'| <o |UNIV :: 'tv::var set| \<Longrightarrow>
    tvsubst_rawpat \<tau> \<sigma> (tvsubst_rawpat \<tau>' \<sigma>' P) = tvsubst_rawpat (tvsubst_typ \<tau> o \<tau>') (\<sigma> o \<sigma>') P"
  by (induct P) (auto simp: tvsubst_typ_comp lfset.map_comp intro!: lfset.map_cong)

lemma tvsubst_rawpat_cong:
  fixes P :: "('tv::var, 'v::var) rawpat"
  shows "|SSupp_typ \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> |SSupp_typ \<tau>'| <o |UNIV :: 'tv::var set| \<Longrightarrow>
  (\<forall>x \<in> PPTVars P. \<tau> x = \<tau>' x) \<Longrightarrow> (\<forall>x \<in> PPVars P. \<sigma> x = \<sigma>' x) \<Longrightarrow>  
  tvsubst_rawpat \<tau> \<sigma> P = tvsubst_rawpat \<tau>' \<sigma>' P"
  by (induct P) (auto intro!: lfset.map_cong tvsubst_typ_cong)

lemma tvsubst_pat_comp:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|SSupp_typ \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> |SSupp_typ \<tau>'| <o |UNIV :: 'tv::var set| \<Longrightarrow> bij \<sigma> \<Longrightarrow> bij \<sigma>' \<Longrightarrow>
    tvsubst_pat \<tau> \<sigma> (tvsubst_pat \<tau>' \<sigma>' P) = tvsubst_pat (tvsubst_typ \<tau> o \<tau>') (\<sigma> o \<sigma>') P"
  by transfer (auto simp: tvsubst_rawpat_comp)

lemma tvsubst_pat_cong:
  fixes P :: "('tv::var, 'v::var) pat"
  shows "|SSupp_typ \<tau>| <o |UNIV :: 'tv::var set| \<Longrightarrow> |SSupp_typ \<tau>'| <o |UNIV :: 'tv::var set| \<Longrightarrow> bij \<sigma> \<Longrightarrow> bij \<sigma>' \<Longrightarrow>
  (\<forall>x \<in> PTVars P. \<tau> x = \<tau>' x) \<Longrightarrow> (\<forall>x \<in> PVars P. \<sigma> x = \<sigma>' x) \<Longrightarrow>  
  tvsubst_pat \<tau> \<sigma> P = tvsubst_pat \<tau>' \<sigma>' P"
  by transfer (auto simp: tvsubst_rawpat_cong)

lemma vvsubst_pat_id[simp]: "vvsubst_pat id id P = P"
  apply transfer
  subgoal for P
    apply (induct P)
     apply (force simp: typ.map_id values_lfin_iff intro!: trans[OF lfset.map_cong_id lfset.map_id])+
    done
  done

mrbnf "('tv :: var, 'v :: var) pat"
  map: vvsubst_pat
  sets:
    free: PTVars
    bound: "PVars"
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
       apply (force simp: typ.map_comp lfset.map_comp values_lfin_iff intro!: lfset.map_cong)+
      done
    done
  subgoal for P f1 f2 g1 g2
    apply (transfer fixing: f1 f2 g1 g2)
    subgoal for P
      apply (induct P)
       apply (fastforce simp: values_lfin_iff Bex_def intro!: typ.map_cong lfset.map_cong)+
      done
    done
  subgoal for f g
    apply (rule ext)
    apply (transfer fixing: f g)
    subgoal for P
      apply (induct P)
       apply (fastforce simp: typ.set_map lfset.set_map values_lfin_iff)+
      done
    done
  subgoal for f g
    apply (rule ext)
    apply (transfer fixing: f g)
    subgoal for P
      apply (induct P)
       apply (fastforce simp: typ.set_map lfset.set_map values_lfin_iff)+
      done
    done
  subgoal by (simp add: infinite_regular_card_order_natLeq)
  subgoal for P
    apply transfer
    subgoal for P
    apply (induct P)
       apply (force simp: typ.FVars_bd lfset.set_bd values_lfin_iff intro!: stable_UNION[OF stable_natLeq])+
      done
    done
  subgoal for P
    apply transfer
    subgoal for P
    apply (induct P)
       apply (force simp: typ.FVars_bd lfset.set_bd ID.set_bd values_lfin_iff intro!: stable_UNION[OF stable_natLeq])+
      done
    done
  subgoal by simp
  subgoal by simp
  done

lemma vvsubst_pat_PVar[simp]:
  "bij g \<Longrightarrow> vvsubst_pat f g (PVar x T) = PVar (g x) (vvsubst_typ f T)"
  by transfer auto

definition "nonrep_PRec X = (\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PVars P \<inter> PVars Q = {})"

lemma nonrep_PRec_alt: "nonrep_PRec X = nonrep_PPRec (map_lfset id Rep_pat X)"
  unfolding nonrep_PRec_def nonrep_PPRec_def
  apply (auto simp: PVars_def)
   apply (metis Int_emptyD lfin_map_lfset)
  apply (meson Int_emptyD lfin_map_lfset)
  done

lemma vvsubst_pat_PRec[simp]:
  "bij g \<Longrightarrow> nonrep_PRec P \<Longrightarrow> vvsubst_pat f g (PRec P) = PRec (map_lfset id (vvsubst_pat f g) P)"
  unfolding PRec_def vvsubst_pat_def nonrep_PRec_alt
  apply (auto simp: lfset.map_comp o_def map_fun_def id_def[symmetric])
     apply (subst (1 2) Abs_pat_inverse)
  using Rep_pat nonrep_rawpat_vvsubst_rawpat apply blast
  apply (auto) []
      apply (metis Rep_pat lfin_map_lfset mem_Collect_eq)
     apply (subst Abs_pat_inject)
  apply (metis (mono_tags, lifting) Rep_pat lfin_map_lfset mem_Collect_eq nonrep_rawpat_PRec
      nonrep_rawpat_vvsubst_rawpat)
  apply (smt (verit, best) Abs_pat_inverse Rep_pat lfin_map_lfset lfset.map_cong_id
      mem_Collect_eq nonrep_rawpat_PRec nonrep_rawpat_vvsubst_rawpat)
     apply (auto simp: lfset.map_comp intro!: lfset.map_cong) []
  apply (smt (z3) Abs_pat_inverse Rep_pat lfin_map_lfset mem_Collect_eq nonrep_PPRec_def
      nonrep_rawpat_PRec nonrep_rawpat_vvsubst_rawpat
      vvsubst_rawpat.simps(2))
  done

lemma PVars_PVar[simp]: "PVars (PVar x T) = {x}"
  by (auto simp: PVars_def PVar_def Abs_pat_inverse)
lemma PVars_PRec[simp]: "nonrep_PRec P \<Longrightarrow> PVars (PRec P) = (\<Union>x \<in> values P. PVars x)"
  apply (auto simp: PVars_def PRec_def Abs_pat_inverse nonrep_PRec_alt lfin_map_lfset lfset.set_map Rep_pat[simplified])
   apply (subst (asm) Abs_pat_inverse; auto simp: lfin_map_lfset Rep_pat[simplified] lfset.set_map)
   apply (subst Abs_pat_inverse; auto simp: lfin_map_lfset Rep_pat[simplified] lfset.set_map)
  done
lemma PTVars_PVar[simp]: "PTVars (PVar x T) = FVars_typ T"
  by (auto simp: PTVars_def PVar_def Abs_pat_inverse)
lemma PTVars_PRec[simp]: "nonrep_PRec P \<Longrightarrow> PTVars (PRec P) = (\<Union>x \<in> values P. PTVars x)"
  apply (auto simp: PTVars_def PRec_def Abs_pat_inverse nonrep_PRec_alt lfin_map_lfset lfset.set_map Rep_pat[simplified])
   apply (subst (asm) Abs_pat_inverse; auto simp: lfin_map_lfset Rep_pat[simplified] lfset.set_map)
   apply (subst Abs_pat_inverse; auto simp: lfin_map_lfset Rep_pat[simplified] lfset.set_map)
  done

end