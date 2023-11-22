theory More_Stream
imports "HOL-Library.Stream" "../Prelim/Prelim"  "../Prelim/Card_Prelim" 
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

lemma sdistinct_def2: "sdistinct xs \<longleftrightarrow> (\<forall>i j. i \<noteq> j \<longrightarrow> snth xs i \<noteq> snth xs j)"
apply safe
  subgoal for i j
   apply(induct "i-j" arbitrary: i j) apply auto
    sorry
  subgoal sorry .
  
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

lemma theN_inj[simp]: "sdistinct vs \<Longrightarrow> v1 \<in> sset vs \<Longrightarrow> v2 \<in> sset vs \<Longrightarrow>
  snth vs (theN vs v1) = snth vs (theN vs v2) \<Longrightarrow> v1 = v2"
using theN_inj1 by (simp add: theN)

lemma inj_on_theN: "sdistinct vs \<Longrightarrow> inj_on (theN vs) (sset vs)"
unfolding inj_on_def by auto

lemma surj_theN: "sdistinct vs \<Longrightarrow> theN vs ` (sset vs) = UNIV"
unfolding image_def by auto (metis sdistinct_def2 snth_sset theN)

lemma bij_betw_theN: "sdistinct vs \<Longrightarrow> bij_betw (theN vs) (sset vs) UNIV"
unfolding bij_betw_def using inj_on_theN surj_theN by auto

lemma theN_snth[simp]: "sdistinct vs \<Longrightarrow> theN vs (snth vs i) = i"
by (metis snth_sset theN theN_inj1)

lemma inj_on_sdistinct_smap: 
"inj_on f (sset xs) \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (smap f xs)"
unfolding sdistinct_def2 inj_on_def apply simp using snth_sset by blast

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
by (simp add: inj_on_def inj_on_sdistinct_smap)

lemma bij_sdistinct_smap'[simp]: 
"bij f \<Longrightarrow> sdistinct (smap f xs) \<longleftrightarrow> sdistinct xs"
by (simp add: inj_on_def inj_on_sdistinct_smap)


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

class infinite_regular =
  assumes large: "|Field (card_suc natLeq)| \<le>o |UNIV::'a set|" and regular: "regularCard |UNIV::'a set|"

lemma infinite_natLeq: "natLeq \<le>o |A| \<Longrightarrow> infinite A"
  using infinite_iff_natLeq_ordLeq by blast

lemma infinite: "infinite (UNIV :: 'a ::infinite_regular set)"
  using ordLeq_transitive[OF ordLess_imp_ordLeq[OF card_suc_greater_set[OF natLeq_card_order ordLeq_refl[OF natLeq_Card_order]]]
    ordIso_ordLeq_trans[OF ordIso_symmetric[OF card_of_Field_ordIso[OF Card_order_card_suc[OF natLeq_card_order]]] large]]
  by (rule infinite_natLeq)

lemma infinite_ex_inj: "\<exists>f :: nat \<Rightarrow> 'a :: infinite_regular. inj f"
  by (rule infinite_countable_subset[OF infinite, simplified])

typedef 'a dstream = "{xs :: 'a :: infinite_regular stream. sdistinct xs}"
  by (auto intro!: exI[of _ "smap (SOME f :: nat \<Rightarrow> 'a. inj f) nats"] inj_on_sdistinct_smap
    someI_ex[OF infinite_ex_inj])

setup_lifting type_definition_dstream

(*
lift_definition dsmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dstream \<Rightarrow> 'a :: infinite_regular dstream" is
  "\<lambda>f xs. if bij f then smap f xs else xs"
  by (auto simp: bij_def intro!: sdistinct_smap elim: inj_on_subset)
*)

lift_definition dsmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dstream \<Rightarrow> 'a :: infinite_regular dstream" is
  "\<lambda>f xs. if inj_on f (sset xs) then smap f xs else xs"
  by (auto intro!: sdistinct_smap elim: inj_on_subset)

lift_definition dsset :: "'a :: infinite_regular dstream \<Rightarrow> 'a set" is "sset" .

lift_definition dsnth :: "'a :: infinite_regular dstream \<Rightarrow> nat \<Rightarrow> 'a" (infixl \<open>!#!\<close> 100) is "snth" .

lift_definition dtheN :: "'a :: infinite_regular dstream \<Rightarrow> 'a \<Rightarrow> nat" is "theN" .

lift_definition dsdrop:: "nat \<Rightarrow> 'a :: infinite_regular dstream \<Rightarrow> 'a dstream" is "sdrop" 
by (metis add_left_cancel sdistinct_def2 sdrop_snth)

lift_definition dstake:: "nat \<Rightarrow> 'a :: infinite_regular dstream \<Rightarrow> 'a list" is "stake" .




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



end