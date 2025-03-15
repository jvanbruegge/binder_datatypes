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

lemma nonrep_rawpat_PRecI:
  assumes
    "(\<forall>x P. (x, P) \<in>\<in> X \<longrightarrow> nonrep_rawpat P)"
    "(\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PPVars P \<inter> PPVars Q = {})"
  shows "nonrep_rawpat (PPRec X :: ('tv::var, 'v::var) rawpat)"
  using assms
  unfolding nonrep_rawpat_def
proof (safe, goal_cases RL)
  case (RL Q)
  then obtain Y where "Q = PPRec Y"
    by (cases Q; simp)
  with RL(3) have "rel_lfset id (rel_rawpat top) X Y" by auto
  then show ?case sorry
qed

lemma nonrep_rawpat_PRec[simp]: "nonrep_rawpat (PPRec X :: ('tv::var, 'v::var) rawpat) \<longleftrightarrow>
  ((\<forall>x P. (x, P) \<in>\<in> X \<longrightarrow> nonrep_rawpat P) \<and>
  (\<forall>x y P Q. x \<noteq> y \<longrightarrow> (x, P) \<in>\<in> X \<longrightarrow> (y, Q) \<in>\<in> X \<longrightarrow> PPVars P \<inter> PPVars Q = {}))"
  using nonrep_rawpat_PRecI[of X] nonrep_rawpat_PRecD1[of X] nonrep_rawpat_PRecD2[of X] by blast

typedef ('tv::var, 'v::var) pat = "{p :: ('tv, 'v) rawpat. nonrep_rawpat p}"
  by (auto intro!: exI[of _ "PPVar undefined undefined"])

setup_lifting type_definition_pat

lift_definition PVar :: "'v \<Rightarrow> 'tv typ \<Rightarrow> ('tv::var, 'v::var) pat" is PPVar
  by auto
(*
lift_definition PRec :: "(label, ('tv::var, 'v::var) pat) lfset \<Rightarrow> ('tv::var, 'v::var) pat" is PPRec
  by auto
*)
end

end