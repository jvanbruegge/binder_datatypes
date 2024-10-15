(* "SUPER" RECURSOR (i.e., restricted to supervariable binders)  *)
theory Super_Recursor
imports BSmall Supervariables ILC_good 
begin


(* RECURSOR PREPARATIONS: *)

thm iLm_inject[no_vars]
thm iLm_inject_super


lemmas iLm_inject_super_strong = iLm_inject_super
[unfolded touchedSuperT_def bsmall_def[symmetric]]

lemma iLm_refreshVrs: 
assumes ds: "dsset xs \<inter> dsset zs = {}" "FFVars e \<inter> dsset zs = {}"
shows "\<exists> ee. iLm (xs::ivar dstream) e = iLm zs ee"
proof-
  let ?A = "FFVars (iLm xs e)"
  have A: "|?A| <o |UNIV::ivar set|" 
  "?A \<inter> (dsset xs \<union> dsset zs) = {}"
  using ILterm.set_bd_UNIV  
  apply blast using ds by auto
  obtain f where f:  
  "bij f \<and> |supp f| <o |UNIV::ivar set| \<and> bij_betw f (dsset xs) (dsset zs) \<and> 
  dsmap f xs = zs \<and> id_on (FFVars (iLm xs e)) f"
  using ex_dsmap''[OF ds(1) A] by auto
  show ?thesis apply(rule exI[of _ "irrename f e"])
  unfolding iLm_inject apply(rule exI[of _ f])
  using f unfolding id_on_def by auto
qed


lemma iLm_inject_super_strong':
assumes bs: "bsmall (ILC.FFVars e)" and bs': "bsmall (ILC.FFVars e')"
and s: "super xs" "super xs'" "super zs" 
and ill: "iLm (xs::ivar dstream) e = iLm xs' e'" 
and zs: "dsset zs \<inter> (dsset xs \<union> dsset xs' \<union> FFVars e \<union> FFVars e') = {}"
shows 
"\<exists>f f'. 
   bij f \<and> |supp f| <o |UNIV::ivar set| \<and> presSuper f \<and> bsmall (supp f) \<and> 
     id_on ((- (dsset xs \<union> dsset zs))) f \<and> id_on (FFVars (iLm xs e)) f \<and> 
     id_on (dsset xs) (f o f) \<and> dsmap f xs = zs \<and> 
   bij f' \<and> |supp f'| <o |UNIV::ivar set| \<and> presSuper f' \<and> bsmall (supp f') \<and> 
     id_on (- (dsset xs' \<union> dsset zs)) f' \<and> id_on (FFVars (iLm xs' e')) f' \<and> 
     id_on (dsset xs') (f' o f') \<and> dsmap f' xs' = zs \<and> 
   irrename f e = irrename f' e'"
proof-  

  obtain ee where il: "iLm xs e = iLm zs ee" 
  using iLm_refreshVrs[of xs zs e] zs by auto
  hence il': "iLm xs' e' = iLm zs ee" using ill by auto

  obtain f where f: "bij f \<and> |supp f| <o |UNIV::ivar set| \<and> bsmall (supp f) \<and>
    presSuper f \<and> id_on (ILC.FFVars (iLm xs e)) f \<and> 
    id_on (- (dsset xs \<union> dsset zs)) f \<and> 
    id_on (dsset xs) (f \<circ> f) \<and> dsmap f xs = zs \<and> irrename f e = ee"
  using iLm_inject_super_strong[OF bs il s(1,3)] by auto

  obtain f' where f': "bij f' \<and> |supp f'| <o |UNIV::ivar set| \<and> bsmall (supp f') \<and>
    presSuper f' \<and> id_on (ILC.FFVars (iLm xs' e')) f' \<and> 
    id_on (- (dsset xs' \<union> dsset zs)) f' \<and> 
    id_on (dsset xs') (f' \<circ> f') \<and> dsmap f' xs' = zs \<and> irrename f' e' = ee"
  using iLm_inject_super_strong[OF bs' il' s(2,3)] by auto

  have io: "id_on (dsset xs \<union> dsset zs) (f \<circ> f)"
  unfolding id_on_def apply simp
      by (smt (verit, ccfv_threshold) ComplI Un_iff 
       bij_betw_def bij_imp_bij_betw comp_apply dsset_dsmap 
       f id_on_def inv_simp1 not_imageI)
 have io': "id_on (dsset xs' \<union> dsset zs) (f' \<circ> f')"
  unfolding id_on_def apply simp
      by (smt (verit, ccfv_threshold) ComplI Un_iff 
       bij_betw_def bij_imp_bij_betw comp_apply dsset_dsmap 
       f' id_on_def inv_simp1 not_imageI)

  show ?thesis apply(rule exI[of _ f]) apply(rule exI[of _ f']) 
  using f f' io io' by auto  
qed
     
(* *)

term good

lemma good_irrename_induct[consumes 1, case_names iVr iAp iLm]:
assumes bs: "good t"
and iiVr: "\<And>xs x. super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> P (iVr (x::ivar))"
and iiAp: "\<And>e1 es2. good e1 \<Longrightarrow> P e1 \<Longrightarrow> 
  (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')  \<Longrightarrow> 
  (\<forall>e2\<in>sset es2. good e2 \<and> P e2) \<Longrightarrow> P (iAp e1 es2)" 
and iiLm: "\<And>xs e. super xs \<Longrightarrow> 
  (\<And>f. bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> bsmall (supp f) \<Longrightarrow> 
      good (irrename f e) \<and> P (irrename f e)) 
  \<Longrightarrow> P (iLm xs e)"
shows "P t"
proof-
  have "\<forall>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and> presSuper f \<and> bsmall (supp f)
  \<longrightarrow> P (irrename f t)"
  using bs proof(induct)
    case (iVr x)
    then show ?case using iiVr 
      by simp (metis dstream.set_map imageI presSuper_def)
  next
    case (iAp t1 t2)
    then show ?case using iiAp  
     by auto (smt (verit, best) image_iff irrename_good stream.set_map touchedSuperT_irrename)
  next
    case (iLm xs t)
    then show ?case using iiLm   
      by simp (smt (verit) bij_o bsmall_supp_comp irrename_good ILterm.rrename_comps ILterm_pre.supp_comp_bound 
      presSuper_comp presSuper_def)
  qed
  thus ?thesis apply(elim allE[of _ id]) by auto
qed



(* RECURSOR *)

locale ILC_SuperRec = 
fixes B :: "'b set"
and iVrB :: "ivar \<Rightarrow> 'b" 
and iApB :: "'b \<Rightarrow> 'b stream \<Rightarrow> 'b"
and iLmB :: "ivar dstream \<Rightarrow> 'b \<Rightarrow> 'b"
and renB :: "(ivar \<Rightarrow> ivar) \<Rightarrow> 'b \<Rightarrow> 'b"
and FVarsB :: "'b \<Rightarrow> ivar set"
assumes 
(* closedness: *)
iVrB_B[simp,intro]: "\<And>xs x. super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> iVrB x \<in> B"
and 
iApB_B[simp,intro]: "\<And>b1 bs2. b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> iApB b1 bs2 \<in> B"
and 
iLmB_B[simp,intro]: "\<And>xs b. b \<in> B \<Longrightarrow> super xs \<Longrightarrow> iLmB xs b \<in> B"
and 
renB_B[simp]: "\<And>\<sigma> b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
  b \<in> B \<Longrightarrow> renB \<sigma> b \<in> B"
and 
(* proper axioms: *)
renB_id[simp,intro]: "\<And>b. b \<in> B \<Longrightarrow> renB id b = b"
and 
renB_comp[simp,intro]: "\<And>b \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
    bij \<tau> \<Longrightarrow> |supp \<tau>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<tau>) \<Longrightarrow> presSuper \<tau> \<Longrightarrow> 
    b \<in> B \<Longrightarrow> renB (\<tau> o \<sigma>) b = renB \<tau> (renB \<sigma> b)"
and 
renB_cong[simp]: "\<And>\<sigma> b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   (\<forall>xs \<in> touchedSuper (FVarsB b). dsmap \<sigma> xs = xs) \<Longrightarrow> 
   renB \<sigma> b = b"
(* and 
NB: This is redundant: 
renB_FVarsB[simp]: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b" 
*)
and 
(* *)
renB_iVrB[simp]: "\<And>\<sigma> x. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
  super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> 
  renB \<sigma> (iVrB x) = iVrB (\<sigma> x)"
and 
renB_iApB[simp]: "\<And>\<sigma> b1 bs2. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow>
   renB \<sigma> (iApB b1 bs2) = iApB (renB \<sigma> b1) (smap (renB \<sigma>) bs2)"
and 
renB_iLmB[simp]: "\<And>\<sigma> xs b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   b \<in> B \<Longrightarrow> super xs \<Longrightarrow> 
   renB \<sigma> (iLmB xs b) = iLmB (dsmap \<sigma> xs) (renB \<sigma> b)"
(* *)
and 
FVarsB_iVrB: "\<And>xs x. super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> touchedSuper (FVarsB (iVrB x)) \<subseteq> touchedSuper {x}"
and 
FVarsB_iApB: "\<And>b1 bs2. b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> 
 touchedSuper (FVarsB (iApB b1 bs2)) \<subseteq> 
 touchedSuper (FVarsB b1) \<union> \<Union> ((touchedSuper o FVarsB) ` (sset bs2))"
and 
FVarsB_iLmB: "\<And>xs b. b \<in> B \<Longrightarrow> super xs \<Longrightarrow> 
  touchedSuper (FVarsB (iLmB xs b)) \<subseteq> touchedSuper (FVarsB b) - {xs}"
begin 

lemma not_in_FVarsB_iLmB: 
"b \<in> B \<Longrightarrow> super xs \<Longrightarrow> touchedSuper (dsset xs \<inter> FVarsB (iLmB xs b)) = {}"
using FVarsB_iLmB unfolding touchedSuper_def by auto

thm iLm_inject_super_strong

lemma iLmB_inject_super_strong_rev: 
assumes bb': "{b,b'} \<subseteq> B" and 
s: "super xs" "super xs'" and 
xs': "dsset xs' \<inter> FVarsB b = {}" and 
f: "bij f" "|supp f| <o |UNIV::ivar set|" "bsmall (supp f)" "presSuper f"
"id_on (- (dsset xs \<union> dsset xs')) f" "dsmap f xs = xs'" and r: "renB f b = b'"
shows "iLmB xs b = iLmB xs' b'"
proof-
  have "\<forall>ys\<in>touchedSuper (FVarsB b - dsset xs). dsmap f ys = ys"
  using s f FVarsB_iLmB bb' xs' unfolding touchedSuper_def 
  by auto (smt (verit, ccfv_SIG) Compl_iff Int_iff dstream.set_map id_on_def 
     image_eqI presSuper_def super_disj) 
  
  hence id: "\<forall>ys\<in>touchedSuper (FVarsB (iLmB xs b)). dsmap f ys = ys"
  using bb' s FVarsB_iLmB super_dsset_singl 
  by auto (smt (z3) Diff_eq_empty_iff Diff_iff FVarsB_iLmB all_not_in_conv disjoint_iff 
  mem_Collect_eq touchedSuper_def) 

  have "iLmB xs b = renB f (iLmB xs b)"
  apply(rule sym) apply(rule renB_cong) using s f bb' FVarsB_iLmB unfolding id_on_def 
  using id unfolding id_on_def by auto
  also have "\<dots> = iLmB xs' b'" apply(subst renB_iLmB) using s f r bb' by auto
  finally show ?thesis .
qed

lemma iLmB_inject_super_strong'_rev: 
assumes bb': "{b,b'} \<subseteq> B"  
and s: "super xs" "super xs'" 
and zs: "dsset zs \<inter> FVarsB b = {}" "dsset zs \<inter> FVarsB b' = {}"
and f: "bij f" "|supp f| <o |UNIV::ivar set|" 
          "id_on (- (dsset xs \<union> dsset zs)) f" "dsmap f xs = zs" 
           "bsmall (supp f)" "presSuper f"
and f': "bij f'" "|supp f'| <o |UNIV::ivar set|" 
          "id_on (- (dsset xs' \<union> dsset zs)) f'" "dsmap f' xs' = zs" 
           "bsmall (supp f')" "presSuper f'"
and r: "renB f b = renB f' b'"
shows "iLmB xs b = iLmB xs' b'" 
proof-
  define c where c: "c = renB f b"
  have c': "c = renB f' b'" unfolding c r ..
  have "iLmB xs b = iLmB zs c"  
  apply(rule iLmB_inject_super_strong_rev[of _ _ _ _ f]) 
  using assms FVarsB_iLmB id_on_def unfolding c apply auto
  unfolding presSuper_def by simp
  also have "iLmB zs c = iLmB xs' b'"  
  apply(rule sym, rule iLmB_inject_super_strong_rev[of _ _ _ _ f']) 
  using assms FVarsB_iLmB id_on_def unfolding c apply auto
  unfolding presSuper_def by simp
  finally show ?thesis .
qed

(* NB: 
We obtain a more general recursor if we replace renB_cong with iLmB_inject_strong_rev; 
and an even more general one if we replace it with iLmB_inject_super_strong'_rev. 
*)


(* *)
definition morFromTrm where 
"morFromTrm H \<equiv> 
 (\<forall>e. good e \<longrightarrow> H e \<in> B) \<and>  
 (\<forall>xs x. super xs \<and> x \<in> dsset xs \<longrightarrow> H (iVr x) = iVrB x) \<and> 
 (\<forall>e1 es2. good e1 \<and> (\<forall>e2\<in>sset es2. good e2) \<and> 
    (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')
    \<longrightarrow> H (iAp e1 es2) = iApB (H e1) (smap H es2)) \<and> 
 (\<forall>xs e. super xs \<and> good e \<longrightarrow> H (iLm xs e) = iLmB xs (H e)) \<and> 
 (\<forall>\<sigma> e. good e \<and> bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::ivar set| \<and> bsmall (supp \<sigma>) \<and> presSuper \<sigma>  
          \<longrightarrow> H (irrename \<sigma> e) = renB \<sigma> (H e)) \<and> 
 (\<forall>e. good e \<longrightarrow> touchedSuper (FVarsB (H e)) \<subseteq> touchedSuper (FFVars e))"

thm good.induct

(* *)

(* *)

inductive R where 
iVr: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> R (iVr x) (iVrB x)"
|
iAp: "R e1 b1 \<Longrightarrow> 
   (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') \<Longrightarrow> 
   stream_all2 R es2 bs2 \<Longrightarrow> 
   R (iAp e1 es2) (iApB b1 bs2)"
|
iLm: "R e b \<Longrightarrow> super xs \<Longrightarrow>  R (iLm xs e) (iLmB xs b)"

(* *)

lemma R_iVr_elim[simp]: "R (iVr x) b \<longleftrightarrow> (\<exists>xs. super xs \<and> x \<in> dsset xs \<and> b = iVrB x)"
apply safe
  subgoal by (cases rule: R.cases) auto
  subgoal by (auto intro: R.intros) .

lemma R_iAp_elim: 
assumes "R (iAp e1 es2) b"
shows "\<exists>b1 bs2. R e1 b1 \<and> (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') \<and> 
               stream_all2 R es2 bs2 \<and> b = iApB b1 bs2"
using assms by (cases rule: R.cases) auto

lemma R_iLm_elim: 
assumes "R (iLm xs e) b"
shows "\<exists>xs' e' b'. super xs' \<and> R e' b' \<and> iLm xs e = iLm xs' e' \<and> b = iLmB xs' b'"
using assms by (cases rule: R.cases) auto

lemma R_total: 
"good e \<Longrightarrow> \<exists>b. b \<in> B \<and> R e b"
proof(induct e rule: good.induct)
  case (iVr xs x)
  then show ?case by auto
next
  case (iAp e1 es2)
  then obtain b1 where b1: "b1 \<in> B" "R e1 b1" by auto
  from iAp(3) obtain E2 where 
  E2: "\<And>e2. e2 \<in> sset es2 \<Longrightarrow> good e2 \<and> (E2 e2) \<in> B \<and> R e2 (E2 e2)" by metis
  term "iApB b1 (smap E2 es2)"
  show ?case apply(rule exI[of _ "iApB b1 (smap E2 es2)"], intro conjI)
    subgoal apply(rule iApB_B) using b1 E2 by auto
    subgoal apply(rule R.iAp) using b1 E2 iAp(4) unfolding stream_all2_iff_snth by auto .   
next
  case (iLm xs e)
  then obtain b where b: "b \<in> B" "R e b" by auto
  show ?case apply(rule exI[of _ "iLmB xs b"], intro conjI)
    subgoal apply(rule iLmB_B) using iLm b by auto
    subgoal apply(rule R.iLm) using iLm b by auto .
qed

lemma R_B: "R e b \<Longrightarrow> b \<in> B"
apply(induct rule: R.induct) 
by simp_all (metis (no_types, lifting) iApB_B stream_all2_iff_snth subsetI theN)

lemma R_good: "R e b \<Longrightarrow> good e"
apply(induct rule: R.induct)  
  subgoal by (intro good.intros) auto
  subgoal apply (intro good.intros)
  unfolding stream_all2_iff_snth sset_range by auto
  subgoal by (intro good.intros) auto .

lemma R_main: 
assumes "good e"
shows 
"(\<forall>b b'. R e b \<longrightarrow> R e b' \<longrightarrow> b = b') \<and> 
 (\<forall>b. R e b \<longrightarrow> touchedSuper (FVarsB b) \<subseteq> touchedSuper (FFVars e)) \<and> 
 (\<forall>b f. R e b \<and> bij f \<and> |supp f| <o |UNIV::ivar set| \<and> presSuper f \<and> bsmall (supp f) 
        \<longrightarrow> R (irrename f e) (renB f b))"
using assms proof(induct e rule: good_irrename_induct)
  case (iVr xs x)
  then show ?case using FVarsB_iVrB 
    by (auto simp: presSuper_def)
next
  case (iAp e1 es2)
  note iAp11 = iAp(2)[THEN conjunct1, rule_format]
  note iAp12 = iAp(2)[THEN conjunct2, THEN conjunct1, rule_format]
  note iAp13 = iAp(2)[THEN conjunct2, THEN conjunct2, rule_format, 
     OF conjI, OF _ conjI, OF _ _ conjI, OF _ _ _ conjI]
  note iAp21 = iAp(4)[rule_format, THEN conjunct2, THEN conjunct1, rule_format]
  note iAp22 = iAp(4)[rule_format, THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note iAp23 = iAp(4)[rule_format, THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format, 
     OF _ conjI, OF _ _ conjI, OF _ _ _ conjI, OF _ _ _ _ conjI]

  note gd = iAp(1) iAp(3)[rule_format]
  iAp(4)[rule_format, THEN conjunct1, rule_format]

  show ?case proof safe 
    fix b b' assume "R (iAp e1 es2) b" "R (iAp e1 es2) b'"
    then obtain b1 bs2 b1' bs2' where R1: "R e1 b1" "R e1 b1'" 
    and R2: "stream_all2 R es2 bs2" "stream_all2 R es2 bs2'" 
    and b: "b = iApB b1 bs2" "b' = iApB b1' bs2'"
    and es2: "(\<forall>e2 e2'. {e2, e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')"
    using R_iAp_elim 
    by meson

    have 1: "b1 = b1'" using iAp11[OF R1] .
    have 2: "bs2 = bs2'" using iAp21 R2 
    unfolding stream_all2_iff_snth sset_range image_def stream_eq_nth by fastforce
    show "b = b'" unfolding b 1 2 ..
  next
    fix b x assume "R (iAp e1 es2) b" and xx: "x \<in> touchedSuper (FVarsB b)"
    then obtain b1 bs2 where R1: "R e1 b1"  
    and R2: "stream_all2 R es2 bs2"  
    and b: "b = iApB b1 bs2"  
    and es2: "(\<forall>e2 e2'. {e2, e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')" 
    using R_iAp_elim by blast

    have b12: "b1 \<in> B" "sset bs2 \<subseteq> B"   
    using R1 R_B  
    by auto (metis R2 R_B stream_all2_iff_snth theN)

    have x: "x \<in> touchedSuper (FVarsB b1) \<or> (\<exists>b2\<in>sset bs2. x \<in> touchedSuper (FVarsB b2))"
    using xx b12 FVarsB_iApB unfolding b by fastforce

    have fb1: "touchedSuper (FVarsB b1) \<subseteq> touchedSuper (FFVars e1)" using iAp12[OF R1] .
    have fb2: "touchedSuper (\<Union> (FVarsB ` (sset bs2))) \<subseteq> 
               touchedSuper (\<Union> (FFVars ` (sset es2)))"
    using iAp22 R2 unfolding stream_all2_iff_snth sset_range image_def touchedSuper_UN 
    by auto

    show "x \<in> touchedSuper (FFVars (iAp e1 es2))" 
    using x fb1 fb2   
    by safe (force simp: touchedSuper_iAp UN_iff touchedSuperT_def touchedSuper_def)+ 

  next
    fix b and f::"ivar \<Rightarrow> ivar" 
    assume "R (iAp e1 es2) b" and f: "bij f" "|supp f| <o |UNIV::ivar set|" 
    "presSuper f" "bsmall (supp f)"
    then obtain b1 bs2 where R1: "R e1 b1"  
    and R2: "stream_all2 R es2 bs2" and b: "b = iApB b1 bs2"  
    using R_iAp_elim by blast

    have b12: "b1 \<in> B" "sset bs2 \<subseteq> B"   
    using R1 R_B  
    by auto (metis R2 R_B stream_all2_iff_snth theN)

    have 0: "R (iAp (irrename f e1) (smap (irrename f) es2)) 
            (iApB (renB f b1) (smap (renB f) bs2))"
    apply(rule R.iAp) 
      subgoal using iAp13[OF R1 f] .
      subgoal using gd f(1) f(2) f(3) touchedSuperT_irrename
      unfolding stream_all2_iff_snth sset_range image_def  
      by fastforce+
      subgoal using iAp23[OF _ _ f] R2
      unfolding stream_all2_iff_snth sset_range image_def by fastforce .

    show "R (irrename f (iAp e1 es2)) (renB f b)"
    unfolding b using 0  
    using gd b12(1) b12(2) f irrename_simps(2) renB_iApB by auto
  qed
next  
  case (iLm xs t)
  note iLmm = iLm(2)[rule_format]
  note iLm1 = iLmm[THEN conjunct2, THEN conjunct1, rule_format]
  note iLm2 = iLmm[THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note iLm3 = iLmm[THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format, 
    OF _ _ _ _ conjI, OF _ _ _ _ _ conjI, OF _ _ _ _ _ _ conjI, OF _ _ _ _ _ _ _ conjI]
  note iLm33 = iLm3[of id, simplified]
  note xs = `super xs` 
  note gd = iLmm[THEN conjunct1, rule_format]
  hence gdt: "good t" by fastforce

  show ?case proof safe
    fix b1 b2 assume RiLm: "R (iLm xs t) b1" "R (iLm xs t) b2" 
    then obtain xs1' t1' b1' xs2' t2' b2'
    where 1: "R t1' b1'" "iLm xs t = iLm xs1' t1'" "b1 = iLmB xs1' b1'"
    and   2: "R t2' b2'" "iLm xs t = iLm xs2' t2'" "b2 = iLmB xs2' b2'"
    and xs1': "super xs1'" and xs2': "super xs2'"
    using R_iLm_elim by metis
    hence s: "super xs" "super xs1'" "super xs2'" using xs by auto

    have gd12': "good t1'" "good t2'" using 1(1) 2(1) R_good by auto

    hence bs: "bsmall (ILC.FFVars t)" and bs1: "bsmall (ILC.FFVars t1')" and bs2: "bsmall (ILC.FFVars t2')"
    using s good_finite_touchedSuperT[OF gd12'(1)] good_finite_touchedSuperT[OF gd12'(2)]
    good_finite_touchedSuperT[OF gdt]
    by (auto simp add: bsmall_def touchedSuperT_def[symmetric]) 

    have b12': "{b1',b2'} \<subseteq> B"
    using 1(1,3) 2(1,3) R_B by auto

    have "bsmall (dsset xs \<union> dsset xs1' \<union> dsset xs2' \<union> FFVars t \<union> FFVars t1' \<union> FFVars t2')"
    apply(intro bsmall_Un) using bs bs1 bs2 s super_bsmall_dsset by auto

    then obtain zs where zs: "super zs"
    and dzs: "dsset zs \<inter> (dsset xs \<union> dsset xs1' \<union> dsset xs2' \<union> FFVars t \<union> FFVars t1' \<union> FFVars t2') = {}" 
    unfolding bsmall_def touchedSuper_def 
    by (smt (verit) Collect_cong Int_commute super_infinite)

    have dzs1: "dsset zs \<inter> (dsset xs \<union> dsset xs1' \<union> ILC.FFVars t \<union> ILC.FFVars t1') = {}"
    using dzs by auto

    obtain f1 f1' where 
    f1: "bij f1" "|supp f1| <o |UNIV::ivar set|"
       "presSuper f1" "bsmall (supp f1)"
       "id_on (- (dsset xs \<union> dsset zs)) f1 \<and> id_on (FFVars(iLm xs t)) f1" 
       "id_on (dsset xs) (f1 o f1)" and 
    f1': "bij f1'" "|supp f1'| <o |UNIV::ivar set|"
       "presSuper f1'" "bsmall (supp f1')"
       "id_on (- (dsset xs1' \<union> dsset zs)) f1' \<and> id_on (FFVars(iLm xs1' t1')) f1'"
       "id_on (dsset xs1') (f1' o f1')" 
    and zs1: "dsmap f1 xs = zs" "dsmap f1' xs1' = zs"
    and f1f1': "irrename f1 t = irrename f1' t1'"   
    using iLm_inject_super_strong'[OF bs bs1 xs xs1' zs 1(2) dzs1] by blast

    have if1': "bij (inv f1' o f1)" "|supp (inv f1' o f1)| <o |UNIV::ivar set|"
    by (auto simp add: f1 f1' ILterm_pre.supp_comp_bound)

    have t1': "t1' = irrename (inv f1' o f1) t"  
    using f1f1' by (metis (mono_tags, lifting) bij_imp_bij_inv f1(1,2) f1'(1,2)
       inv_o_simp1 supp_inv_bound ILterm.rrename_comps ILterm.rrename_ids)

    have ps1: "presSuper (inv f1' \<circ> f1)" "bsmall (supp (inv f1' \<circ> f1))"
      subgoal by (simp add: f1'(1) f1'(2) f1'(3) f1(1) f1(2) f1(3) presSuper_comp presSuper_inv)
      subgoal by (simp add: bsmall_supp_comp bsmall_supp_inv f1'(1) f1'(2) f1'(3) f1'(4) f1(4)) .

    have fvb1': "touchedSuper (FVarsB b1') \<subseteq> touchedSuper (FFVars t1')"
    apply(rule iLm2[OF if1', unfolded t1'[symmetric]])
    by fact+

    have dzs2: "dsset zs \<inter> (dsset xs \<union> dsset xs2' \<union> ILC.FFVars t \<union> ILC.FFVars t2') = {}"
    using dzs by auto

    obtain f2 f2' where 
    f2: "bij f2" "|supp f2| <o |UNIV::ivar set|"
       "presSuper f2" "bsmall (supp f2)"
       "id_on (- (dsset xs \<union> dsset zs)) f2 \<and> id_on (FFVars(iLm xs t)) f2"
       "id_on (dsset xs) (f2 o f2)" and 
    f2': "bij f2'" "|supp f2'| <o |UNIV::ivar set|"
       "presSuper f2'" "bsmall (supp f2')"
       "id_on (- (dsset xs2' \<union> dsset zs)) f2' \<and> id_on (FFVars(iLm xs2' t2')) f2'"
       "id_on (dsset xs2') (f2' o f2')"
    and zs2: "dsmap f2 xs = zs" "dsmap f2' xs2' = zs"
    and f2f2': "irrename f2 t = irrename f2' t2'" 
    using iLm_inject_super_strong'[OF bs bs2 xs xs2' zs 2(2) dzs2] by blast   

    have if2': "bij (inv f2' o f2)" "|supp (inv f2' o f2)| <o |UNIV::ivar set|"
    by (auto simp add: f2 f2' ILterm_pre.supp_comp_bound)

    have t2': "t2' = irrename (inv f2' o f2) t"  
    using f2f2' 
    by (metis (mono_tags, lifting) bij_imp_bij_inv f2(1,2) f2'(1,2)
      inv_o_simp1 ILterm.rrename_comps ILterm.rrename_ids supp_inv_bound)

    have ps2: "presSuper (inv f2' \<circ> f2)" "bsmall (supp (inv f2' \<circ> f2))"
      subgoal by (simp add: f2'(1-3) f2(1-3) presSuper_comp presSuper_inv)
      subgoal by (simp add: bsmall_supp_comp bsmall_supp_inv f2'(1-4) f2(4)) .

    have fvb2': "touchedSuper (FVarsB b2') \<subseteq> touchedSuper (FFVars t2')"
    apply(rule iLm2[OF if2', unfolded t2'[symmetric]])
    by fact+

    have if2: "bij (inv f2)" "|supp (inv f2)| <o |UNIV::ivar set|" 
    "bij_betw (inv f2) (dsset zs) (dsset xs)"
    apply (auto simp add: f2(1,2))
    by (metis bij_bij_betw_inv bij_imp_bij_betw dstream.set_map f2(1) f2(2) zs2(1))

    have bbe: "bij_betw f1 (dsset xs) (dsset zs)"
    "bij_betw f2' (dsset xs2') (dsset zs)"
    apply (metis bij_imp_bij_betw dstream.set_map f1(1) f1(2) zs1(1))
    by (metis bij_betw_def bij_imp_bij_betw dsset_dsmap f2'(1) zs2(2))

    have iif2: "id_on (- (dsset xs \<union> dsset zs)) (inv f2)"
    using f2(1,3,5) id_on_inv by blast

    have eo1: "eq_on (dsset xs) f1 (inv f1)"
    using f1(1,5,6) unfolding id_on_def eq_on_def   
    by simp (metis inv_simp1)  

    have eo2: "eq_on (dsset xs) f2 (inv f2)"
    using f2(1,5,6) unfolding id_on_def eq_on_def  
    by simp (metis inv_simp1)

    have eq_f1f2: "eq_on (dsset zs) (inv f1) (inv f2)" 
    by (metis bbe(1) bij_betw_imp_inj_on bij_bij_betw_inv 
      dsmap_eq2 dstream.map_comp f1(1) f1(2) f2(1) f2(2) if2(3) 
      inv_o_simp1 supp_inv_bound zs1(1) zs2(1))

    have eq_f1f2: "eq_on (dsset xs) (inv f1) (inv f2)" 
    by (metis bbe(1) bij_betw_imp_inj_on bij_bij_betw_inv dsmap_eq2 eo1 eo2 eq_on_sym eq_on_trans f2(1) if2(3) zs1(1) zs2(1))

    have id_f1f2: "id_on (dsset xs) (f1 o inv f2)" 
    by (smt (verit, best) bij_inv_eq_iff comp_apply eq_f1f2 eq_onD f1(1) id_on_def)
    
    define ff2' where "ff2' = f1 o (inv f2) o f2'"
  
    have ff2': "bij ff2'" "|supp ff2'| <o |UNIV::ivar set|" 
       "presSuper ff2'" "bsmall (supp ff2')"
       "id_on (- (dsset xs2' \<union> dsset zs)) ff2' \<and> id_on (FFVars (iLm xs2' t2')) ff2'" 
    unfolding ff2'_def using f1 f2 f2'  
      subgoal by auto 
      subgoal unfolding ff2'_def using f1 f2 f2' by (simp add: ILterm_pre.supp_comp_bound)
      subgoal  
        by (simp add: f1(1) f1(2) f1(3) f2'(1) f2'(2) f2'(3) f2(1) f2(2) f2(3) ILterm_pre.supp_comp_bound presSuper_comp presSuper_inv)
      subgoal using bsmall_supp_comp bsmall_supp_inv f1(4) f2'(4) f2(1) f2(2) f2(3) f2(4) by auto
      subgoal apply(rule conjI)  
        subgoal unfolding ff2'_def using f1 f2 f2' eo2
        unfolding id_on_def eq_on_def apply simp by (metis bij_inv_eq_iff eq_f1f2 eq_on_def)
        subgoal unfolding ff2'_def using f1 f2 f2' iif2  eo2
        unfolding id_on_def eq_on_def apply simp  
        by (metis bbe(2) bij_betw_def comp_apply id_f1f2 id_on_def not_imageI) . .

    have zz2: "dsmap ff2' xs2' = zs"
    by (metis bbe(1) bbe(2) bij_betw_def bij_bij_betw_inv comp_eq_dest_lhs dsnth_dsmap 
          dsnth_dsmap_cong f2(1) ff2'_def if2(3) inv_simp1 zs1(1) zs2(1) zs2(2))
 
    have rew1: "irrename f1' (irrename (inv f1' \<circ> f1) t) = irrename f1 t" 
    using f1f1' t1' by auto

    have rew2: "irrename ff2' (irrename (inv f2' \<circ> f2) t) = irrename f1 t" 
    by (smt (verit, best) bij_betw_comp_iff bij_is_inj f1(1) f1(2) f2'(1) f2'(2) f2(1) f2(2) f2f2' 
            ff2'_def if2(2) ILterm.rrename_comps ILterm.supp_comp_bound o_inv_o_cancel t2')

    show "b1 = b2" unfolding 1(3) 2(3) 
    apply(rule iLmB_inject_super_strong'_rev[OF b12', of xs1' xs2' zs f1' ff2'])
      subgoal by fact  subgoal by fact
      subgoal using zs dzs fvb1' unfolding touchedSuper_def by auto
      subgoal using zs dzs fvb2' unfolding touchedSuper_def by auto
      subgoal using f1' by auto  subgoal using f1' by auto
      subgoal using f1' by auto  subgoal using zs1 by auto
      subgoal by fact  subgoal by fact
      subgoal using ff2' by auto  subgoal using ff2' by auto
      subgoal using ff2' by auto  subgoal using zz2 by auto 
      subgoal by fact  subgoal by fact
      subgoal apply(rule iLm1[OF f1(1,2)])  
        subgoal by fact  subgoal by fact
        subgoal using iLm3[OF if1' ps1 1(1)[unfolded t1'] f1'(1-4), unfolded rew1] .
        subgoal using iLm3[OF if2' ps2 2(1)[unfolded t2'] ff2'(1-4), unfolded rew2] . . .

  (* *)
  next
    fix b ys
    assume R: "R (iLm xs t) b" and yys: "ys \<in> touchedSuper (FVarsB b)"
    then obtain xs' t' b'
    where 0: "R t' b'" "iLm xs t = iLm xs' t'" "b = iLmB xs' b'" 
    and xs': "super xs'"
    using R_iLm_elim by metis

    have gd': "good t'" using 0(1) R_good by auto

    hence bs: "bsmall (FFVars t)" and bs': "bsmall (FFVars t')" 
    using xs' good_finite_touchedSuperT[OF gd'] 
    good_finite_touchedSuperT[OF gdt]
    by (auto simp add: bsmall_def touchedSuperT_def[symmetric]) 

    have b': "b' \<in>  B"
    using 0(1,3) R_B by auto

    have ys: "dsset ys \<inter> dsset xs' = {}" "ys \<in> touchedSuper (FVarsB b')" using b' yys unfolding 0 
    using FVarsB_iLmB[OF b' xs'] xs' (*unfolding touchedSuper_def *) 
    by auto (metis (no_types, lifting) DiffD2 insertCI mem_Collect_eq subsetD touchedSuper_def touchedSuper_iVr)

    have "bsmall (dsset xs \<union> dsset xs' \<union> FFVars t \<union> FFVars t')"
    apply(intro bsmall_Un) using bs bs' xs xs' super_bsmall_dsset by auto   

    obtain f where 
    f: "bij f" "|supp f| <o |UNIV::ivar set|" 
    "id_on (FFVars (iLm xs t)) f" "presSuper f" "bsmall (supp f)"
    and zs: "dsmap f xs = xs'"   
    and t': "t' = irrename f t" 
    using iLm_inject_super_strong[OF bs 0(2) xs xs'] by auto
    
    have fvb't': "touchedSuper (FVarsB b') \<subseteq> touchedSuper (FFVars t')"
    using iLm2[OF f(1,2), unfolded t'[symmetric], OF f(4,5) 0(1)] .
    have yt': "ys \<in> touchedSuper (FFVars t')" using fvb't' ys(2) by auto

    show "ys \<in> touchedSuper (FFVars (iLm xs t))" 
    using yt' ys unfolding 0(2) touchedSuper_def by auto

  (* *)
  next
    fix b and f :: "ivar\<Rightarrow>ivar"
    assume "R (iLm xs t) b" and f: "bij f" "|supp f| <o |UNIV::ivar set|" 
    " presSuper f" "bsmall (supp f)"
    then obtain xs' t' b'
    where 0: "R t' b'" "iLm xs t = iLm xs' t'" "b = iLmB xs' b'" 
    and xs': "super xs'"
    using R_iLm_elim by metis

    have gd': "good t'" using 0(1) R_good by auto

    hence bs: "bsmall (FFVars t)" and bs': "bsmall (FFVars t')" 
    using xs' good_finite_touchedSuperT[OF gd'] 
    good_finite_touchedSuperT[OF gdt]
    by (auto simp add: bsmall_def touchedSuperT_def[symmetric]) 
 
    have b': "b' \<in>  B"
    using 0(1,3) R_B by auto

    have "|dsset xs \<union> dsset xs' \<union> FFVars t \<union> FFVars t'| <o |UNIV::ivar set|"
    by (meson card_dsset_ivar ILterm.set_bd_UNIV var_stream_class.Un_bound)
  
    (* then obtain zs where zs: 
    "dsset zs \<inter> (dsset xs \<union> dsset xs' \<union> FFVars t \<union> FFVars t') = {}" 
    using iLm_avoid by blast *)

    obtain g where g: "bij g" "|supp g| <o |UNIV::ivar set|" 
    "presSuper g" "bsmall (supp g)"
    "id_on (FFVars (iLm xs t)) g" 
    and z: "dsmap g xs = xs'"   
    and t': "t' = irrename g t"
    using iLm_inject_super_strong[OF bs 0(2) xs xs'] by auto  

    have RR: "R (iLm (dsmap f xs') (irrename f t')) (iLmB (dsmap f xs') (renB f b'))"
    apply(rule R.iLm) unfolding t' apply(rule iLm3)
      subgoal by fact  subgoal by fact  subgoal by fact  subgoal by fact
      subgoal using 0(1) unfolding t' .
      subgoal by fact subgoal by fact subgoal by fact subgoal by fact 
      subgoal using f(3) presSuper_def xs' by blast .

    show "R (irrename f (iLm xs t)) (renB f b)" 
    unfolding 0 using RR apply(subst irrename_simps) 
      subgoal using f by auto subgoal using f by auto
      subgoal apply(subst renB_iLmB) using xs' f b' by auto .  
  qed
qed

lemmas R_functional = R_main[THEN conjunct1, rule_format]
lemmas R_FFVars= R_main[THEN conjunct2, THEN conjunct1, rule_format]
lemmas R_irrename = R_main[THEN conjunct2, THEN conjunct2, rule_format]

(* *)

definition H :: "ilterm \<Rightarrow> 'b" where "H t \<equiv> SOME b. b \<in> B \<and> R t b"

lemma H_B_R: "good t \<Longrightarrow> H t \<in> B \<and> R t (H t)"
by (metis (no_types, lifting) H_def R_total someI_ex)

lemmas H_B = H_B_R[THEN conjunct1]
lemmas H_R = H_B_R[THEN conjunct2]

lemma H_eqI: "good t \<Longrightarrow> R t b \<Longrightarrow> H t = b"
using H_B_R R_functional by blast

lemma R_iff_H: "good t \<Longrightarrow> R t b \<longleftrightarrow> H t = b"
using H_R R_functional by auto


lemma ex_morFromTrm: "\<exists>H. morFromTrm H"
apply(rule exI[of _ H]) unfolding morFromTrm_def apply(intro conjI)
  subgoal using R_B H_R by auto
  subgoal apply safe apply(rule H_eqI) apply(rule good.iVr) by auto
  subgoal apply safe apply(rule H_eqI)
    subgoal apply(rule good.iAp) by auto
    subgoal apply(rule R.iAp)  
    using H_R unfolding stream_all2_iff_snth sset_range image_def by fastforce+ .
  subgoal apply safe apply(rule H_eqI)
    subgoal apply(rule good.iLm) by auto
    subgoal apply(rule R.iLm)  
    using H_R by auto .
  subgoal apply safe apply(rule H_eqI)
    subgoal using irrename_good by auto
    subgoal apply(rule R_irrename) using H_R by auto .
  subgoal using R_FFVars R_iff_H by auto .

(* *)

definition rec where "rec \<equiv> SOME H. morFromTrm H"

lemma morFromTrm_rec: "morFromTrm rec"
by (metis ex_morFromTrm rec_def someI_ex)

(* *)

lemma rec_B[simp,intro!]: "good e \<Longrightarrow> rec e \<in> B" 
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iVr[simp]: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> rec (iVr x) = iVrB x"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iAp[simp]: "good e1 \<Longrightarrow> (\<forall>e2\<in>sset es2. good e2) \<Longrightarrow> 
 (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') \<Longrightarrow>
 rec (iAp e1 es2) = iApB (rec e1) (smap rec es2)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iLm[simp]: "super xs \<Longrightarrow> good e \<Longrightarrow> rec (iLm xs e) = iLmB xs (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_irrename: "good e \<Longrightarrow> bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
 rec (irrename \<sigma> e) = renB \<sigma> (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma FVarsB_rec: "good e \<Longrightarrow> touchedSuper (FVarsB (rec e)) \<subseteq> touchedSuper (FFVars e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_unique: 
assumes gd: "good e"
and "\<And>e. good e \<Longrightarrow> H e \<in> B" 
"\<And>xs x. super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> H (iVr x) = iVrB x" 
"\<And>e1 es2. good e1 \<Longrightarrow> (\<forall>e2\<in>sset es2. good e2) \<Longrightarrow> 
(\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') \<Longrightarrow>
H (iAp e1 es2) = iApB (H e1) (smap H es2)"
"\<And>xs e. super xs \<Longrightarrow> good e \<Longrightarrow> H (iLm xs e) = iLmB xs (H e)"
shows "H e = rec e" 
using gd apply(induct e)
using assms by (auto cong: stream.map_cong)  

end (* context ILC_SuperRec *)

end 