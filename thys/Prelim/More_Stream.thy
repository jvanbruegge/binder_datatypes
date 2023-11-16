theory More_Stream
imports "HOL-Library.Stream" "../Prelim/Prelim"  "../Prelim/Card_Prelim" 
begin 

(* More on streams: *)

definition sdistinct where 
"sdistinct xs \<equiv> \<forall>i j. i \<noteq> j \<longrightarrow> snth xs i \<noteq> snth xs j"

lemmas stream.set_map[simp] lemmas stream.map_id[simp]

lemma sset_natLeq: "|sset vs| \<le>o natLeq"
by (metis card_of_image countable_card_of_nat countable_card_le_natLeq sset_range)

definition theN where 
"theN vs v \<equiv> SOME i. snth vs i = v"

lemma theN: "v \<in> sset vs \<Longrightarrow> snth vs (theN vs v) = v"
unfolding theN_def apply(rule someI_ex) by (metis imageE sset_range)

lemma theN_inj1: "sdistinct vs \<Longrightarrow> v \<in> sset vs \<Longrightarrow>  
  snth vs i = snth vs (theN vs v) \<Longrightarrow> i = theN vs v"
using theN[of v vs] unfolding sdistinct_def by fastforce

lemma theN_inj[simp]: "sdistinct vs \<Longrightarrow> v1 \<in> sset vs \<Longrightarrow> v2 \<in> sset vs \<Longrightarrow>
  snth vs (theN vs v1) = snth vs (theN vs v2) \<Longrightarrow> v1 = v2"
using theN_inj1 by (simp add: theN)

lemma inj_on_theN: "sdistinct vs \<Longrightarrow> inj_on (theN vs) (sset vs)"
unfolding inj_on_def by auto

lemma surj_theN: "sdistinct vs \<Longrightarrow> theN vs ` (sset vs) = UNIV"
unfolding image_def by auto (metis sdistinct_def snth_sset theN)

lemma bij_betw_theN: "sdistinct vs \<Longrightarrow> bij_betw (theN vs) (sset vs) UNIV"
unfolding bij_betw_def using inj_on_theN surj_theN by auto

lemma theN_snth[simp]: "sdistinct vs \<Longrightarrow> theN vs (snth vs i) = i"
by (metis snth_sset theN theN_inj1)

lemma inj_on_sdistinct_smap: 
"inj_on f (sset xs) \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (smap f xs)"
unfolding sdistinct_def inj_on_def apply simp using snth_sset by blast

lemma sdistinct_smap: 
"sdistinct (smap f xs) \<Longrightarrow> sdistinct xs"
unfolding sdistinct_def by auto metis

lemma inj_on_sdistinct_smap'[simp]: 
"inj_on f (sset xs) \<Longrightarrow> sdistinct (smap f xs) \<longleftrightarrow> sdistinct xs"
by (meson inj_on_sdistinct_smap sdistinct_smap)

lemma bij_sdistinct_smap: 
"bij f \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (smap f xs)"
by (simp add: inj_on_def inj_on_sdistinct_smap)

lemma bij_sdistinct_smap'[simp]: 
"bij f \<Longrightarrow> sdistinct (smap f xs) \<longleftrightarrow> sdistinct xs"
by (simp add: inj_on_def inj_on_sdistinct_smap)

end