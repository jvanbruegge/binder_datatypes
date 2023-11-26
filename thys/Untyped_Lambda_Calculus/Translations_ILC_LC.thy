(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory Translations_ILC_LC
imports ILC_relations_more
begin

(* Translating finitary lambda to (affine, uniform) infinitary-lambda *)

(* the range of supervariables: *)
definition "RSuper \<equiv> \<Union> (dsset ` (range superOf))"

lemma super_dsset_RSuper: "super xs \<Longrightarrow> dsset xs \<subseteq> RSuper"
by (metis RSuper_def UN_iff range_eqI subsetI superOf_subOf)

lemma RSuper_def2: "RSuper = \<Union> (dsset ` {xs. super xs})"
unfolding RSuper_def apply auto 
  using super_superOf apply blast  
  by (metis superOf_subOf)

definition theSN where 
"theSN x \<equiv> SOME xs_i. super (fst xs_i) \<and> x = dsnth (fst xs_i) (snd xs_i)"

lemma theSN': "x \<in> RSuper \<Longrightarrow> super (fst (theSN x)) \<and> x = dsnth (fst (theSN x)) (snd (theSN x))"
unfolding theSN_def RSuper_def apply(rule someI_ex)  
by simp (metis dtheN super_superOf)  

lemma theSN: "x \<in> RSuper \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super xs \<and> dsnth xs i = x"
by (metis fst_conv snd_conv theSN')

lemma theSN_unique: 
"x \<in> RSuper \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super ys \<and> dsnth ys j = x \<Longrightarrow> ys = xs \<and> j = i"
by (metis Int_emptyD dsset_range dtheN_dsnth rangeI super_disj theSN) 

lemma theSN_ex: "super xs \<Longrightarrow> \<exists> x \<in> RSuper. (xs,i) = theSN x"
by (metis (full_types) RSuper_def Union_iff dsset_range imageI rangeI super_imp_superOf surjective_pairing theSN_unique)

(* This summarizes the only properties we are interested in about theSN, 
which in turn will be used to prove the correctness of the supervariable-based 
renaming extension. 
It ways that theSN is a bijection between 
(1) the set of all variables that appear in supervariables 
and 
(2) the pairs (xs,n) indicating specific supervariables xs and positions n (where the 
variable is located)
*)



lemma bij_theSN: 
"bij_betw theSN RSuper ({xs. super xs} \<times> (UNIV::nat set))"
unfolding bij_betw_def inj_on_def apply auto
  apply (metis theSN')
  apply (meson UnionI imageI rangeI theSN)
  by (metis imageI theSN_ex)



(* Extending a renaming on variables to one on ivariables via "superOf"; 
essentially, renaming is applied in block to all "super-variables", 
and those ivars that do not participate in supervariables are left unchanged.
*)
definition ext :: "(var \<Rightarrow> var) \<Rightarrow> ivar \<Rightarrow> ivar" where 
"ext f x \<equiv> if x \<in> RSuper 
   then let (xs,i) = theSN x in dsnth (superOf (f (subOf xs))) i
   else x"

lemma bij_ext: "bij f \<Longrightarrow> bij (ext f)" 
unfolding bij_def inj_on_def surj_def ext_def apply (auto split: prod.splits simp: image_def)
  apply (metis Int_emptyD dsnth.rep_eq dsset.rep_eq dtheN_dsnth snth_sset subOf_superOf superOf_subOf super_disj super_superOf theSN)
   apply (metis RSuper_def UN_iff dsset_range range_eqI)  
  apply (metis super_superOf theSN theSN_ex)  
  by (metis prod.inject subOf_superOf superOf_subOf super_superOf theSN theSN_ex) 
  
lemma supp_ext: "supp (ext f) \<subseteq> {x. \<exists>xs. x \<in> dsset xs \<and> super xs \<and> subOf xs \<in> supp f}"
unfolding supp_def  apply auto 
by (smt (verit, del_insts) case_prod_conv dsset_range ext_def prod.collapse range_eqI superOf_subOf theSN')

lemma supp_ext': "supp (ext f) \<subseteq> \<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))"
using supp_ext by fastforce

lemma card_supp_ext: 
assumes "|supp f| <o |UNIV::var set|"
shows "|supp (ext f)| <o |UNIV::ivar set|"
proof-
  have "|supp (ext f)| \<le>o |\<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))|"
  using supp_ext' card_of_mono1 by blast
  also have "|\<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))| \<le>o 
             |Sigma ({xs . super xs} \<inter> subOf -` (supp f)) dsset|"
  using card_of_UNION_Sigma .
  also have "|Sigma ({xs . super xs} \<inter> subOf -` (supp f)) dsset| \<le>o |UNIV::var set|"
  apply(rule card_of_Sigma_ordLeq_infinite)
    subgoal by (simp add: infinite_var)
    subgoal by (metis Int_left_absorb bij_betw_def bij_superOf inf_le2 le_inf_iff surj_imp_ordLeq) 
    subgoal using dsset_natLeq card_var ordIso_iff_ordLeq ordLeq_transitive by blast .
  also have "|UNIV::var set| <o |UNIV::ivar set|" 
    using card_var_ivar .
  finally show ?thesis .
qed

lemma super_dsmap_ext: "super xs \<Longrightarrow> super (dsmap (ext f) xs)"
unfolding ext_def by (smt (z3) case_prod_conv dsnth_dsmap_cong fst_conv snd_conv super_superOf theSN' theSN_ex)

lemma ext_comp: "ext (g o f) = ext g o ext f"
apply(rule ext) unfolding ext_def apply (auto split: prod.splits) 
  apply (metis subOf_superOf super_superOf theSN_unique)
  using super_superOf theSN theSN_ex by blast

lemma ext_inv: "bij f \<Longrightarrow> ext (inv f) = inv (ext f)"
by (metis (no_types, lifting) bij_ext bij_id comp_assoc ext_comp inv_id inv_o_simp1 inv_o_simp2 inv_unique_comp)

lemma super_dsmap_ext': 
assumes f: "bij f" "|supp f| <o |UNIV::var set|" and s: "super (dsmap (ext f) xs)"
shows "super xs"  
proof-
  have 0: "dsmap (ext (inv f)) ((dsmap (ext f) xs)) = xs"
  apply(subst dstream.map_comp) using f 
  by (auto simp add: bij_ext card_supp_ext bij_ext ext_inv)  
  have "super (dsmap (ext (inv f)) ((dsmap (ext f) xs)))"
  using s using super_dsmap_ext by auto 
  thus ?thesis unfolding 0 .
qed

lemma presSuper_ext: "bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow> presSuper (ext f)"
unfolding presSuper_def using super_dsmap_ext super_dsmap_ext' by blast

lemma touchedSuper_supp: "touchedSuper (supp (ext f)) \<subseteq> superOf ` (supp f)"
using supp_ext[of f]  apply auto sledgehammer

(* *)

consts tr :: "trm \<Rightarrow> nat list \<Rightarrow> itrm"

axiomatization where 
tr_Var[simp]: "tr (Var x) p = iVar (dsnth (superOf x) (natOf p))"
and 
tr_Lam[simp]: "tr (Lam x e) p = iLam (superOf x) (tr e p)"
and 
tr_App[simp]: "tr (App e1 e2) p = iApp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)"

lemma FFVars_tr: 
"{subOf xs | xs . dsset xs \<inter> ILC.FFVars (tr e p) \<noteq> {}} \<subseteq> LC.FFVars e"
sorry
  
lemma rrename_tr:
assumes "bij f" and "|supp f| <o |UNIV::var set|"
shows "tr (rrename f e) p = irrename (ext f) (tr e p)"
sorry


end 
