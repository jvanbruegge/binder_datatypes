theory More_Stream
imports "HOL-Library.Stream" "Binders.Classes"
begin 

(* More on streams: *)

(* update a stream at an index: *)
definition "supd xs i y \<equiv> shift (stake i xs) (SCons y (sdrop (Suc i) xs))"

lemma snth_supd: "snth (supd xs i y) j = (if i = j then y else snth xs j)"
unfolding supd_def apply(split if_splits) apply safe
  subgoal by auto
  subgoal apply(cases "j < i") 
    subgoal by auto 
    subgoal by simp (metis Suc_diff_Suc add_diff_inverse_nat not_less_iff_gr_or_eq sdrop_snth 
                     sdrop_stl snth.simps(2) snth_Stream) . .

lemma snth_supd_same[simp]: "snth (supd xs i y) i = y"
unfolding snth_supd by auto

lemma snth_supd_diff[simp]: "j \<noteq> i \<Longrightarrow> snth (supd xs i y) j = snth xs j"
unfolding snth_supd by auto

lemma smap_supd[simp]: "smap f (supd xs i y) = supd (smap f xs) i (f y)"
by (simp add: supd_def)

(* *)

coinductive sdistinct where
  "x \<notin> sset s \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (x ## s)"

lemma sdistinct_stl: "sdistinct s \<Longrightarrow> sdistinct (stl s)"
  by (erule sdistinct.cases) simp

lemma sdistinct_fromN[simp]: "sdistinct (fromN n)"
  by (coinduction arbitrary: n) (subst siterate.code,  auto)

lemma sdistinct_stl_snthD: "sdistinct xs \<Longrightarrow> xs !! i \<noteq> stl xs !! i"
  by (induct i arbitrary: xs) (force elim: sdistinct.cases)+

lemma sdistinct_shd_snthD: "sdistinct xs \<Longrightarrow> i > 0 \<Longrightarrow> shd xs \<noteq> xs !! i"
  by (induct i arbitrary: xs) (force elim: sdistinct.cases)+

lemma sdistinct_def2: "sdistinct xs \<longleftrightarrow> (\<forall>i j. i \<noteq> j \<longrightarrow> snth xs i \<noteq> snth xs j)"
  apply safe
  subgoal for i j
    apply (cases "i < j")
    subgoal
    proof(induct i arbitrary: j xs)
      case 0
      then show ?case
        by (simp add: sdistinct_shd_snthD)
    next
      case (Suc i)
      from Suc(1)[of "stl xs"] Suc(2-) show ?case
        by (force simp: Suc_less_eq2 sdistinct_stl)
    qed
    subgoal
    proof(induct j arbitrary: i xs)
      case 0
      then show ?case
        by (simp add: sdistinct_shd_snthD[symmetric])
    next
      case (Suc j)
      from Suc(1)[of "stl xs" "i - 1"] Suc(2-) show ?case
        by (cases i) (auto simp: not_less Suc_le_eq sdistinct_stl)
    qed
    done
  subgoal
    apply (coinduction arbitrary: xs)
    subgoal for xs
      apply (cases xs)
      apply (auto simp: sset_range)
       apply force
      apply (metis snth_Stream)
      done . .
  
lemmas stream.set_map[simp] lemmas stream.map_id[simp]

lemma sset_natLeq: "|sset vs| \<le>o natLeq"
by (metis card_of_image countable_card_of_nat countable_card_le_natLeq sset_range)

definition theN where 
"theN vs v \<equiv> SOME i. snth vs i = v"

lemma theN: "v \<in> sset vs \<Longrightarrow> snth vs (theN vs v) = v"
unfolding theN_def apply(rule someI_ex) by (metis imageE sset_range)

lemma theN_inj1: "sdistinct vs \<Longrightarrow> v \<in> sset vs \<Longrightarrow>  
  snth vs i = snth vs (theN vs v) \<Longrightarrow> i = theN vs v"
using theN[of v vs] unfolding sdistinct_def2 by fastforce

lemma theN_inj: "sdistinct vs \<Longrightarrow> v1 \<in> sset vs \<Longrightarrow> v2 \<in> sset vs \<Longrightarrow>
  snth vs (theN vs v1) = snth vs (theN vs v2) \<Longrightarrow> v1 = v2"
using theN_inj1 by (simp add: theN)

lemma inj_on_theN: "sdistinct vs \<Longrightarrow> inj_on (theN vs) (sset vs)"
unfolding inj_on_def by (auto simp: theN_inj)

lemma surj_theN: "sdistinct vs \<Longrightarrow> theN vs ` (sset vs) = UNIV"
unfolding image_def by auto (metis sdistinct_def2 snth_sset theN)

lemma bij_betw_theN: "sdistinct vs \<Longrightarrow> bij_betw (theN vs) (sset vs) UNIV"
unfolding bij_betw_def using inj_on_theN surj_theN by auto

lemma theN_snth[simp]: "sdistinct vs \<Longrightarrow> theN vs (snth vs i) = i"
by (metis snth_sset theN theN_inj1)

lemma inj_on_sdistinct_smap: 
"inj_on f (sset xs) \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (smap f xs)"
unfolding sdistinct_def2 inj_on_def apply simp using snth_sset by blast

lemma smap_eq: 
"smap f xs = xs \<longleftrightarrow> id_on (sset xs) f"
by (metis (full_types) id_on_def snth_smap stream.map_ident_strong theN)

lemma smap_eq2: 
"smap f xs = smap g xs \<longleftrightarrow> eq_on (sset xs) f g"
by (smt (verit, best) eq_on_def snth_smap stream.map_cong0 theN)

(* 
lemma sdistinct_smap: "inj_on f (sset s) \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (smap f s)"
  by (coinduction arbitrary: s)
    (auto simp: smap_ctr stream.set_map inj_on_def stream.set_sel sdistinct_stl elim: sdistinct.cases)
*)

lemma sdistinct_smap: 
"sdistinct (smap f xs) \<Longrightarrow> sdistinct xs"
unfolding sdistinct_def2 by auto metis

lemma inj_on_sdistinct_smap'[simp]: 
"inj_on f (sset xs) \<Longrightarrow> sdistinct (smap f xs) \<longleftrightarrow> sdistinct xs"
by (meson inj_on_sdistinct_smap sdistinct_smap)

lemma bij_sdistinct_smap: 
"bij f \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (smap f xs)"
by (simp add: inj_on_def inj_on_sdistinct_smap bij_implies_inject)

lemma bij_sdistinct_smap'[simp]: 
"bij f \<Longrightarrow> sdistinct (smap f xs) \<longleftrightarrow> sdistinct xs"
by (simp add: inj_on_def inj_on_sdistinct_smap bij_implies_inject)


lemma sdistinct_inj_snth: "sdistinct xs \<Longrightarrow> inj (snth xs)"
unfolding sset_range inj_on_def sdistinct_def2 by auto

lemma sdistinct_snth_inj[simp]: "sdistinct xs \<Longrightarrow> snth xs i = snth xs j \<longleftrightarrow> i = j"
by (metis theN_snth)

lemma stream_eq_nth: "xs = ys \<longleftrightarrow> (\<forall>i. snth xs i = snth ys i)"
by (metis smap_alt stream_smap_nats)

lemma inj_ex_snth: 
assumes "inj f"
shows "\<exists>xs. sdistinct xs \<and> (\<forall>n. snth xs n = f n)"
by (metis assms atLeast_0 inj_on_sdistinct_smap sdistinct_fromN snth_smap sset_fromN stream_smap_nats theN_snth)

(* *) 
lemma set_stake: "set (stake i xs) = snth xs ` {..<i}"
unfolding set_conv_nth by force

lemma set_sdrop: "sset (sdrop i xs) = snth xs ` {i ..}"
unfolding sset_range apply auto 
apply (simp add: sdrop_snth) 
by (metis add_diff_inverse_nat not_less rangeI sdrop_snth)


lemma sset_supd[simp]: "sset (supd es i e) = {snth es j | j . j \<noteq> i} \<union> {e}"
unfolding supd_def apply auto unfolding set_sdrop set_stake apply auto
  apply (metis Suc_n_not_le_n snth.simps(2))
  by (metis atLeast_iff imageI lessThan_iff not_less not_less_eq_eq not_less_iff_gr_or_eq 
    sdrop.simps(2) set_sdrop)

lemma stream_all2_iff_snth: "stream_all2 P xs ys \<longleftrightarrow> (\<forall>i. P (snth xs i) (snth ys i))"
unfolding stream_all2_def BNF_Def.Grp_def apply auto 
  using in_mono apply fastforce unfolding OO_def apply auto 
  apply(rule exI[of _ "szip xs ys"]) apply auto 
  apply (simp add: stream_eq_nth)  
  apply (metis fst_conv prod.sel(2) snth_szip theN)
  apply (simp add: stream_eq_nth)  
  apply (metis fst_conv prod.sel(2) snth_szip theN) .

lemma sset_smap2: "sset (smap2 f xs ys) = {(f (snth xs i) (snth ys i)) | i . True}"
unfolding sset_range by auto

(* *)

definition build2stream where 
"build2stream f \<equiv> smap (\<lambda>i. smap (\<lambda>j. f i j) nats) nats"

lemma snth_build2stream[simp]: "snth (snth (build2stream f) i) j = f i j"
unfolding build2stream_def by auto

(* *)

definition nat2 :: "nat \<Rightarrow> nat \<times> nat" where 
"nat2 \<equiv> SOME f. bij f"

lemma bij_nat2: "bij nat2" 
by (metis bij_prod_decode nat2_def someI_ex)

definition nat1 :: "nat \<times> nat \<Rightarrow> nat" where 
"nat1 \<equiv> inv nat2"

lemma bij_nat1: "bij nat1" 
by (simp add: bij_nat2 nat1_def)

lemma nat2_inj[simp]: "nat2 u = nat2 v \<longleftrightarrow> u = v"
using bij_nat2 by (force simp: bij_implies_inject)

lemma nat1_inj[simp]: "nat1 u = nat1 v \<longleftrightarrow> u = v"
using bij_nat1 by (force simp: bij_implies_inject)

lemma nat1_nat2[simp]: "nat1 (nat2 u) = u"
by (simp add: bij_nat2 nat1_def)

lemma nat2_nat1[simp]: "nat2 (nat1 u) = u"
by (simp add: bij_nat2 nat1_def)

fun snth2 where "snth2 xss (i,j) = snth (snth xss i) j"

definition sflat :: "'a stream stream \<Rightarrow> 'a stream" where 
"sflat xss \<equiv> smap (\<lambda>i. snth2 xss (nat2 i)) nats"

lemma snth_sflat: "snth (sflat xss) i = snth2 xss (nat2 i)"
by (simp add: sflat_def)

lemma smap_sflat: "smap f (sflat xss) = sflat (smap (smap f) xss)"
unfolding sflat_def 
unfolding stream.map_comp apply(rule stream.map_cong0) 
subgoal for z by (cases "nat2 z", auto) . 

lemma sset_sflat: "sset (sflat xss) = \<Union> (sset ` (sset xss))"
unfolding sset_range image_def apply (auto simp: snth_sflat) 
apply (smt (verit, ccfv_threshold) mem_Collect_eq snth2.elims) 
by (metis bij_inv_eq_iff bij_nat2 snth2.simps)

lemma ex_sflat: "\<exists>tss. ts = sflat tss"
apply(rule exI[of _ "build2stream (\<lambda> i j. snth ts (nat1 (i,j)))"])
unfolding stream_eq_nth apply safe
subgoal for i apply(cases "nat2 i") unfolding snth_sflat  
by simp (metis nat1_nat2) . 

(* *)

lemma infinite_natLeq: "natLeq \<le>o |A| \<Longrightarrow> infinite A"
  using infinite_iff_natLeq_ordLeq by blast

lemmas infinite = infinite_UNIV

lemma infinite_ex_inj: "\<exists>f :: nat \<Rightarrow> 'a :: covar. inj f"
  by (rule infinite_countable_subset[OF infinite, simplified])

typedef 'a dstream = "{xs :: 'a :: covar stream. sdistinct xs}"
  by (auto intro!: exI[of _ "smap (SOME f :: nat \<Rightarrow> 'a. inj f) nats"] inj_on_sdistinct_smap
    someI_ex[OF infinite_ex_inj])

setup_lifting type_definition_dstream

lift_definition dsmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dstream \<Rightarrow> 'a :: covar dstream" is
  "\<lambda>f xs. if inj_on f (sset xs) then smap f xs else xs"
  by (auto intro!: sdistinct_smap elim: inj_on_subset)

lift_definition dsset :: "'a :: covar dstream \<Rightarrow> 'a set" is "sset" .

lift_definition dsnth :: "'a :: covar dstream \<Rightarrow> nat \<Rightarrow> 'a" (infixl \<open>!#!\<close> 100) is "snth" .

lift_definition dtheN :: "'a :: covar dstream \<Rightarrow> 'a \<Rightarrow> nat" is "theN" .

lift_definition dsdrop:: "nat \<Rightarrow> 'a :: covar dstream \<Rightarrow> 'a dstream" is "sdrop" 
by (metis add_left_cancel sdistinct_def2 sdrop_snth)

lift_definition dstake:: "nat \<Rightarrow> 'a :: covar dstream \<Rightarrow> 'a list" is "stake" .




lemma countable_sset:
  fixes s
  notes * = LeastI[where P="\<lambda>i. s !! i = s !! _", OF refl]
  shows "countable (sset s)"
  unfolding sset_range
  by (intro countableI[where f="\<lambda>x. LEAST i. snth s i = x"] inj_onI, elim imageE, hypsubst_thin)
    (rule box_equals[OF _ * *], simp)

lemma dsset_natLeq: "|dsset vs| \<le>o natLeq"
apply transfer using sset_natLeq by auto

lemma dsset_range: "dsset s = range (dsnth s)"
apply transfer using sset_range by metis

lemma dsset_dsmap[simp]: "inj_on f (dsset vs) \<Longrightarrow> dsset (dsmap f vs) = f ` dsset vs"
apply transfer by auto

lemma dsmap_alt: "inj_on f (dsset vs) \<Longrightarrow> dsmap f vs = vs' \<longleftrightarrow> (\<forall>n. f (dsnth vs n) = dsnth vs' n)" 
apply transfer by (auto simp: smap_alt)

lemma dsnth_dsmap: "inj_on f (dsset vs) \<Longrightarrow> dsnth (dsmap f vs) n = f (dsnth vs n)"
apply transfer using snth_smap by metis

(* *)

lemma dtheN: "v \<in> dsset vs \<Longrightarrow> dsnth vs (dtheN vs v) = v"
apply transfer using theN by metis

lemma dtheN_inj1: "v \<in> dsset vs \<Longrightarrow>  
  dsnth vs i = dsnth vs (dtheN vs v) \<Longrightarrow> i = dtheN vs v"
apply transfer using theN_inj1 by metis

lemma dtheN_inj[simp]: "v1 \<in> dsset vs \<Longrightarrow> v2 \<in> dsset vs \<Longrightarrow>
  dsnth vs (dtheN vs v1) = dsnth vs (dtheN vs v2) \<Longrightarrow> v1 = v2"
apply transfer using theN_inj by metis

lemma inj_on_dtheN: "inj_on (dtheN vs) (dsset vs)"
apply transfer using inj_on_theN by metis

lemma surj_dtheN: "dtheN vs ` (dsset vs) = UNIV"
apply transfer using surj_theN by metis

lemma bij_betw_dtheN: "bij_betw (dtheN vs) (dsset vs) UNIV"
apply transfer using bij_betw_theN by metis

lemma dtheN_dsnth[simp]: "dtheN vs (dsnth vs i) = i"
apply transfer using theN_snth by metis

lemma inj_dsnth: "inj (dsnth xs)"
apply transfer using sdistinct_inj_snth by auto

lemma dsnth_inj[simp]: "dsnth xs i = dsnth xs j \<longleftrightarrow> i = j"
apply transfer by auto

lemma dstream_eq_nth: "xs = ys \<longleftrightarrow> (\<forall>i. dsnth xs i = dsnth ys i)"
apply transfer unfolding stream_eq_nth by auto

lemma inj_ex_dsnth: 
"inj f \<Longrightarrow> \<exists>xs. \<forall>n. dsnth xs n = f n"
apply transfer using inj_ex_snth by auto


thm stream.map_cong0[no_vars]

lemma dsmap_cong: "inj_on f (dsset xs) \<Longrightarrow> inj_on g (dsset xs) \<Longrightarrow>  
 (\<And>z. z \<in> dsset xs \<Longrightarrow> f z = g z) \<Longrightarrow> dsmap f xs = dsmap g xs"
apply transfer by (auto cong: stream.map_cong0)  


lemmas dsnth_dsmap[simp]

lemma dsnth_dsmap_cong: "(\<And>i. f (dsnth xs i) = dsnth ys i) \<Longrightarrow> dsmap f xs = ys"
by (metis (no_types, opaque_lifting) dsmap_alt dtheN dtheN_dsnth inj_onCI)

lemma ex_dsmap: "\<exists>f. bij_betw f (dsset xs) (dsset ys) \<and> dsmap f xs = ys \<and> id_on (- dsset xs) f"
apply(rule exI[of _ "\<lambda>x. if x \<in> dsset xs then dsnth ys (dtheN xs x) else x"])
unfolding bij_betw_def inj_on_def apply (simp add: dsmap_alt inj_on_def) 
by (smt (verit, ccfv_SIG) ComplD dsset_range id_on_def image_cong image_image range_eqI surj_dtheN)

lemma countable_dsset: "countable (dsset xs)" 
by (simp add: countable_sset dsset.rep_eq)

lemma dsset_card_le: "|dsset xs| \<le>o |UNIV::nat set|"
using countable_card_of_nat countable_dsset by blast

lemma dsset_card_ls: "|dsset xs| <o |UNIV::'a :: covar set|"
proof-
  have "|dsset xs| <o |Field (card_suc natLeq)|" 
    using Card_order_iff_ordLeq_card_of Card_order_card_suc 
    card_suc_greater_set dsset_natLeq natLeq_card_order ordLess_ordLeq_trans by blast
  thus ?thesis
    using covar_class.large ordLess_ordLeq_trans by blast
qed

lemma ex_dsmap': 
assumes ds: "dsset xs \<inter> dsset ys = {}"
shows "\<exists>f::'a\<Rightarrow>'a. bij f \<and> |supp f| <o |UNIV::'a :: covar set| \<and> 
   bij_betw f (dsset xs) (dsset ys) \<and> dsmap f xs = ys"
proof-
  obtain f where f: "bij_betw f (dsset xs) (dsset ys)" "dsmap f xs = ys"
  using ex_dsmap by auto
  obtain u where u: "bij u \<and> |supp u| <o |UNIV::'a :: covar set| \<and> 
     bij_betw u (dsset xs) (dsset ys) \<and> eq_on (dsset xs) u f" 
  using ex_bij_betw_supp_UNIV[OF _ _ f(1) ds, where C = "{}", simplified]  
  using dsset_card_ls infinite by blast
  show ?thesis apply(rule exI[of _ u])
  using u f(2) apply auto  
  by (meson bij_betw_imp_inj_on dsmap_cong eq_on_def f(1))
qed

lemma ex_dsmap'': 
assumes ds: "dsset xs \<inter> dsset ys = {}" and 
A: "|A| <o |UNIV::'a :: covar set|" "A \<inter> (dsset xs \<union> dsset ys) = {}"
shows "\<exists>f::'a\<Rightarrow>'a. bij f \<and> |supp f| <o |UNIV::'a :: covar set| \<and> 
   bij_betw f (dsset xs) (dsset ys) \<and> dsmap f xs = ys \<and> 
   id_on A f"
proof-
  obtain f where f: "bij_betw f (dsset xs) (dsset ys)" "dsmap f xs = ys"
  using ex_dsmap by auto
  obtain u where u: "bij u \<and> |supp u| <o |UNIV::'a :: covar set| \<and> 
     bij_betw u (dsset xs) (dsset ys) \<and> imsupp u \<inter> A = {} \<and> eq_on (dsset xs) u f" 
  using ex_bij_betw_supp_UNIV[OF _ _ f(1) ds, where C = "A", simplified]  
  using A dsset_card_ls infinite by blast
  show ?thesis apply(rule exI[of _ u])
  using u f(2) unfolding imsupp_def id_on_def supp_def apply auto  
  by (meson bij_betw_imp_inj_on dsmap_cong eq_on_def f(1)) 
qed

lemma dsmap_eq: 
"inj_on f (dsset xs) \<Longrightarrow> dsmap f xs = xs \<longleftrightarrow> id_on (dsset xs) f"
apply transfer using smap_eq by auto

lemma dsmap_eq2: 
"inj_on f (dsset xs) \<Longrightarrow> inj_on g (dsset xs) \<Longrightarrow> dsmap f xs = dsmap g xs \<longleftrightarrow> eq_on (dsset xs) f g"
apply transfer using smap_eq2 by auto

lemma dssset_dsmap': "bij f \<Longrightarrow> dsset (dsmap f vs) = f ` dsset vs"
apply(rule dsset_dsmap) unfolding bij_def inj_def inj_on_def by auto


end
