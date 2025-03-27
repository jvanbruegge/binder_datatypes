theory Prelim imports Card_Prelim
begin 

hide_type var
hide_const In1

abbreviation "any \<equiv> undefined" 

(* Equal on *)
definition eqlOn :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where 
"eqlOn A u v \<equiv> \<forall> a \<in> A. u a = v a"

lemma eqlOn_refl[simp,intro!]: "eqlOn A u u" unfolding eqlOn_def by auto
lemma eqlOn_sym: "eqlOn A u v \<Longrightarrow> eqlOn A v u" unfolding eqlOn_def by auto
lemma eqlOn_trans: "eqlOn A u v \<Longrightarrow> eqlOn A v w \<Longrightarrow> eqlOn A u w" unfolding eqlOn_def by auto
lemma eqlOn_sub: "B \<subseteq> A \<Longrightarrow> eqlOn A u v \<Longrightarrow> eqlOn B u v" unfolding eqlOn_def by auto

definition eqlOnN :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where 
"eqlOnN i u v \<equiv> \<forall> j < i. u j = v j"

lemma eqlOnN_refl[simp,intro!]: "eqlOnN i u u" unfolding eqlOnN_def by auto
lemma eqlOnN_sym: "eqlOnN i u v \<Longrightarrow> eqlOnN i v u" unfolding eqlOnN_def by auto
lemma eqlOnN_trans: "eqlOnN i u v \<Longrightarrow> eqlOnN i v w \<Longrightarrow> eqlOnN i u w" unfolding eqlOnN_def by auto
lemma eqlOnN_leq: "j \<le> i \<Longrightarrow> eqlOnN i u v \<Longrightarrow> eqlOnN j u v" unfolding eqlOnN_def by auto


(* A notion of "clean" bijection between: *) 
definition "bijBtw f A B \<equiv> bij_betw f A B \<and> f \<in> Func A B"

lemma bij_betw_bijBtw:
assumes "bij_betw f A B"
shows "\<exists>g. bijBtw g A B \<and> eqlOn A g f"
proof-
  let ?g = "\<lambda>a. if a \<in> A then f a else any"
  show ?thesis 
  apply(rule exI[of _ ?g]) using assms 
  unfolding bij_betw_def bijBtw_def eqlOn_def inj_on_def Func_def by  auto
qed

lemma card_of_ordIso_bijBtw: 
"(\<exists>f. bijBtw f A B) \<longleftrightarrow> |A| =o |B|"
  by (meson bijBtw_def bij_betw_bijBtw card_of_ordIso)

definition "invBtw f A B \<equiv> 
  SOME g. g \<in> Func B A \<and> (\<forall>a\<in>A. g (f a) = a) \<and> (\<forall>b\<in>B. f (g b) = b)"

lemma invBtw:
assumes "bijBtw f A B"
defines "g \<equiv> invBtw f A B"  
shows "g \<in> Func B A \<and> (\<forall>a\<in>A. g (f a) = a) \<and> (\<forall>b\<in>B. f (g b) = b)" (is "?\<phi> g")
proof-
  define h where "h \<equiv> restrict (inv_into A f) B"
  have "?\<phi> h" using assms bij_betw_inv_into unfolding Func_def h_def
  by (smt (verit) bijBtw_def bij_betwE bij_betw_inv_into_left mem_Collect_eq restrict_apply)
  thus ?thesis unfolding g_def invBtw_def by (rule someI[of ?\<phi>])  
qed

lemmas invBtw_Func = invBtw[THEN conjunct1]
lemmas bijBtw_invBtw_left = invBtw[THEN conjunct2, THEN conjunct1, rule_format]
lemmas bijBtw_invBtw_right = invBtw[THEN conjunct2, THEN conjunct2, rule_format]

thm bij_betw_inv_into[no_vars]

lemma bijBtw_invBtw: 
assumes "bijBtw f A B" 
shows "bijBtw (invBtw f A B) B A"
using assms invBtw[OF assms]  
unfolding bijBtw_def  
apply (auto intro!: bij_betw_byWitness)
apply (meson Func_elim) 
using bij_betwE by blast  

lemma ex_bijBtw_nat_finite: 
"finite M \<Longrightarrow> \<exists>h. bijBtw h {0..<card M} M"
  by (meson bij_betw_bijBtw ex_bij_betw_nat_finite)

definition idOn :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a" where 
"idOn A \<equiv> \<lambda>a. if a\<in>A then a else any"

lemma bijBwt_idOn: "bijBtw (idOn A) A A"
unfolding bijBtw_def idOn_def bij_betw_def inj_on_def Func_def by auto


lemma compose_idOnL: "f \<in> Func A A' \<Longrightarrow> compose A f (idOn A) = f"
unfolding compose_def idOn_def Func_def by auto

lemma compose_idOnR: "f \<in> Func A' A \<Longrightarrow> compose A' (idOn A) f = f"
unfolding compose_def idOn_def Func_def by auto

(* *)
lemmas bij_imp_bij_inv[simp]

hide_const compose

(* *)
lemma list_induct_Pair[case_names Nil Cons]: 
"P [] \<Longrightarrow> (\<And>z1 z2 z1z2s. P z1z2s  \<Longrightarrow> P ((z1,z2) # z1z2s)) \<Longrightarrow> P z1z2s"
by (metis list.inducts surj_pair)


end