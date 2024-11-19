theory ILC
  imports
 "Prelim.FixedUncountableVars"
 "Prelim.Swapping_vs_Permutation"
 "Binders.General_Customization"
 "Prelim.More_Stream"
begin

(* We register distinct streams: *)
mrbnf "'a ::uncountable_regular dstream"
  map: dsmap
  sets: bound: dsset
  bd: "card_suc natLeq"
  var_class: uncountable_regular
  subgoal by (rule ext, transfer) simp
  subgoal apply (rule ext, transfer) by (simp add: stream.map_comp inj_on_def)
  subgoal apply transfer by (simp cong: stream.map_cong inj_on_cong)
  subgoal apply (rule ext, transfer) by (simp add: inj_on_def)
  subgoal by (rule infinite_regular_card_order_card_suc[OF natLeq_card_order natLeq_Cinfinite])
  subgoal
    apply (rule card_suc_greater_set[OF natLeq_card_order])
    apply transfer
    apply (simp flip: countable_card_le_natLeq add: countable_sset)
    done
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done

lemma dstream_map_comp:
"bij f \<Longrightarrow> |supp (f::'a\<Rightarrow>'a)| <o |UNIV::('a ::uncountable_regular) set| \<Longrightarrow> bij g \<Longrightarrow> |supp g| <o |UNIV::('a ::uncountable_regular) set| \<Longrightarrow>
 dsmap g o dsmap f = dsmap (g \<circ> f)"
apply(rule ext)
using dstream.map_comp[of f g] by auto

thm dstream.map_cong[no_vars]

lemma dstream_map_ident_strong: "(\<And>z. z \<in> dsset t \<Longrightarrow> f z = z) \<Longrightarrow> dsmap f t = t"
by (metis Rep_dstream_inject dsmap.rep_eq dsset.rep_eq stream.map_ident_strong)

lemmas dstream.set_map[simp] lemmas dstream.map_id[simp]

(* DATATYPE DECLARATION  *)

declare [[inductive_internals]]
declare [[mrbnf_internals]]

(*infinitary untyped lambda calculus*)
binder_datatype 'a iterm
  = iVar 'a
  | iApp "'a iterm" "'a iterm stream"
  | iLam "(xs::'a) dstream" t::"'a iterm" binds xs in t
for
  vvsubst: ivvsubst
  tvsubst: itvsubst

declare [[show_consts]]
lemma ex_inj_infinite_regular_var_iterm_pre:
  "\<exists>f :: 'a :: countable \<Rightarrow> 'b :: var_iterm_pre. inj f"
  unfolding card_of_ordLeq[of UNIV UNIV, simplified]
  apply (rule ordLeq_transitive[OF _ var_iterm_pre_class.large])
  apply (rule ordLeq_transitive[OF countable_card_le_natLeq[THEN iffD1]])
  apply simp
  apply (rule natLeq_ordLeq_cinfinite)
  apply (rule iterm_pre.bd_Cinfinite)
  done

definition embed :: "'a :: countable \<Rightarrow> 'b :: var_iterm_pre"
  ("{{_}}" [999] 1000)  where
  "embed = (SOME f. inj f)"

lemma inj_embed: "inj embed"
  unfolding embed_def
  by (rule someI_ex[OF ex_inj_infinite_regular_var_iterm_pre[where 'a='a]])


(****************************)
(* DATATYPE-SPECIFIC CUSTOMIZATION  *)


(* Monomorphising: *)

lemma bd_iterm_pre_ordIso: "bd_iterm_pre =o card_suc natLeq"
  apply (rule ordIso_symmetric)
  apply (tactic \<open>unfold_tac @{context} [Thm.axiom @{theory} "ILC.iterm_pre.bd_iterm_pre_def"]\<close>)
  apply (rule ordIso_transitive[OF _ dir_image_ordIso])
    apply (rule ordIso_symmetric)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Cinfinite_csum Field_natLeq natLeq_card_order natLeq_cinfinite)
      apply (simp add: infinite_regular_card_order.Cnotzero infinite_regular_card_order_natLeq)
     apply (simp add: Field_natLeq natLeq_card_order ordLeq_csum1)
    apply (rule ordIso_transitive)
     apply (rule csum_absorb2)
      apply (simp add: Card_order_cprod Cinfinite_csum1 cinfinite_cprod natLeq_Cinfinite)
     apply (simp add: Card_order_cprod Cinfinite_csum1 cinfinite_cprod natLeq_Cinfinite natLeq_ordLeq_cinfinite)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Card_order_csum cinfinite_cprod cinfinite_csum natLeq_Cinfinite)
      apply (simp add: infinite_regular_card_order.Cnotzero infinite_regular_card_order_natLeq)
     apply (simp add: Card_order_csum cinfinite_cprod cinfinite_csum natLeq_Cinfinite natLeq_ordLeq_cinfinite)
    apply (rule ordIso_transitive)
     apply (rule csum_absorb2)
      apply (simp add: Card_order_cprod cinfinite_cprod cinfinite_csum natLeq_Cinfinite)
     apply (simp add: cprod_mono1 bd_stream_def csum_com ordIso_imp_ordLeq)
    apply (rule ordIso_transitive)
     apply (rule cprod_infinite1')
       apply (simp add: Card_order_csum cinfinite_csum natLeq_Cinfinite)
      apply (simp add: Cinfinite_Cnotzero natLeq_Cinfinite)
     apply (simp add: natLeq_Cinfinite ordLeq_csum2)
    apply (simp add: csum_absorb1 infinite_regular_card_order.Card_order infinite_regular_card_order.cinfinite infinite_regular_card_order_card_suc natLeq_Cinfinite natLeq_card_order natLeq_ordLeq_cinfinite)
  using Card_order_cprod card_order_on_well_order_on apply blast
  unfolding inj_on_def
  apply (tactic \<open>unfold_tac @{context} [Typedef.get_info @{context} @{type_name iterm_pre_bdT} |> hd |> snd |> #Abs_inject OF [UNIV_I, UNIV_I]]\<close>)
  apply simp
  done

lemma natLeq_less_UNIV: "natLeq <o |UNIV :: 'a :: var_iterm_pre set|"
  apply (rule ordLess_ordLeq_trans[OF _ iterm.var_large])
  apply (rule ordLess_ordIso_trans[OF card_suc_greater[OF natLeq_card_order]])
  apply (rule ordIso_symmetric[OF bd_iterm_pre_ordIso])
  done

instantiation ivar :: var_iterm_pre begin
instance
  apply standard
     apply (rule ordLeq_ordIso_trans[OF _ ordIso_symmetric[OF card_ivar]])
     apply (rule ordIso_ordLeq_trans[OF card_of_Field_ordIso])
      apply (tactic \<open>resolve_tac @{context} [BNF_Def.bnf_of @{context} @{type_name stream} |> the |> BNF_Def.bd_Card_order_of_bnf] 1\<close>)
     apply (simp add: bd_stream_def card_suc_least le_card_ivar natLeq_Cinfinite natLeq_card_order)
    apply (rule regularCard_ivar)
  using Field_natLeq infinite_iff_card_of_nat infinite_ivar apply auto[1]
  apply (rule ordIso_ordLeq_trans[OF card_of_Field_ordIso])
  apply (simp add: Card_order_card_suc natLeq_card_order)
  apply (metis card_of_Card_order card_of_card_order_on card_of_nat card_suc_alt card_suc_least countable_card_ivar countable_card_le_natLeq ordIso_imp_ordLeq)
  done
end

definition iVariable :: "nat \<Rightarrow> ivar" where "iVariable \<equiv> ILC.embed"

lemma iVariable_inj: "inj iVariable"
unfolding iVariable_def by (metis inj_embed)

lemma inj_iVariable[simp]: "iVariable n = iVariable m \<longleftrightarrow> n = m"
by (meson injD iVariable_inj)

type_synonym itrm = "ivar iterm"

(* Some lighter notations: *)
abbreviation "VVr \<equiv> tvVVr_itvsubst"
lemmas VVr_def = tvVVr_itvsubst_def
abbreviation "isVVr \<equiv> tvisVVr_itvsubst"
lemmas isVVr_def = tvisVVr_itvsubst_def
abbreviation "IImsupp \<equiv> IImsupp_iterm"
lemmas IImsupp_def = IImsupp_iterm_def
abbreviation "SSupp \<equiv> SSupp_iterm"
lemmas SSupp_def = SSupp_iterm_def
abbreviation "FFVars \<equiv> FVars_iterm"

abbreviation "irrename \<equiv> permute_iterm"
(* *)

lemma FFVars_itvsubst[simp]:
  assumes "|SSupp (\<sigma> :: ivar \<Rightarrow> itrm)| <o |UNIV :: ivar set|"
  shows "FFVars (itvsubst \<sigma> t) = (\<Union> {FFVars (\<sigma> x) | x . x \<in> FFVars t})"
  apply (binder_induction t avoiding: "IImsupp \<sigma>" rule: iterm.strong_induct)
  apply (rule iterm.fresh_induct[of "IImsupp \<sigma>"])
     apply (auto simp: IImsupp_def assms intro!: Un_bound UN_bound iterm.set_bd_UNIV)
  using iterm.FVars_VVr apply (fastforce simp add: SSupp_def)
  using iterm.FVars_VVr apply (auto simp add: SSupp_def Int_Un_distrib)
   apply (smt (verit) disjoint_insert(1) empty_iff insertE insert_absorb iterm.FVars_VVr mem_Collect_eq)
  apply (smt (verit, del_insts) CollectI IntI UN_iff UnCI empty_iff insertE iterm.FVars_VVr)
  done

(* Enabling some simplification rules: *)
lemmas iterm.tvsubst_VVr[simp]
lemmas iterm.FVars_VVr[simp]
iterm.permute_id[simp] iterm.permute_cong_id[simp]
iterm.FVars_permute[simp]

lemma singl_bound: "|{a}| <o |UNIV::ivar set|"
  by (simp add: finite_card_ivar)

lemma ls_UNIV_iff_finite: "|A| <o |UNIV::ivar set| \<longleftrightarrow> countable A"
using countable_iff_le_card_ivar by blast

lemma supp_id_update_le[simp,intro]:
"|supp (id(x := y))| <o |UNIV::ivar set|"
by (metis finite.emptyI finite_insert finite_ordLess_infinite2 imsupp_id_fun_upd imsupp_supp_bound infinite_ivar)

lemma IImsupp_VVr_empty[simp]: "IImsupp VVr = {}"
  unfolding IImsupp_def
  iterm.SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
  done

(* VVr is here the Var constructor: *)
lemma VVr_eq_Var[simp]: "VVr = iVar"
  unfolding VVr_def iVar_def comp_def
  tv\<eta>_iterm_itvsubst_def
  by (rule refl)

(* *)
(* Properties of term-for-variable substitution *)

lemma itvsubst_VVr_func[simp]: "itvsubst VVr t = t"
  apply (rule iterm.TT_fresh_induct)
  apply (rule emp_bound)
  subgoal for x
    apply (rule case_split[of "isVVr (iterm_ctor x)"])
     apply (unfold isVVr_def)[1]
     apply (erule exE)
    subgoal premises prems for a
      unfolding prems
      apply (rule iterm.tvsubst_VVr)
      apply (rule iterm.SSupp_VVr_bound)
        done
      apply (rule trans)
       apply (rule iterm.tvsubst_cctor_not_isVVr)
          apply (rule iterm.SSupp_VVr_bound)
      unfolding IImsupp_VVr_empty
         apply (rule Int_empty_right)
      unfolding noclash_iterm_def Int_Un_distrib Un_empty
        apply assumption+
      apply (rule arg_cong[of _ _ iterm_ctor])
      apply (rule trans)
      apply (rule iterm_pre.map_cong)
                 apply (rule supp_id_bound bij_id)+
           apply (assumption | rule refl)+
      unfolding id_def[symmetric] iterm_pre.map_id
      apply (rule refl)
      done
    done

thm iterm.strong_induct[of "\<lambda>\<rho>. A" "\<lambda>t \<rho>. P t", rule_format, no_vars]

lemma itvsubst_cong:
assumes f: "|SSupp f| <o |UNIV::ivar set|" and g: "|SSupp g| <o |UNIV::ivar set|"
and eq: "(\<And>z. (z::ivar) \<in> FFVars P \<Longrightarrow> f z = g z)"
shows "itvsubst f P = itvsubst g P"
using eq proof (binder_induction P avoiding: "IImsupp f" "IImsupp g" rule: iterm.strong_induct)
  case (iApp x1 x2)
  then show ?case using f g by simp (metis stream.map_cong0)
next
  case (iLam x1 x2)
  then show ?case  using f g apply simp
    by (smt (verit, ccfv_threshold) IImsupp_def SSupp_def UnCI insert_absorb insert_disjoint(2) mem_Collect_eq)
qed (auto simp: IImsupp_def iterm.UNION_bound iterm.Un_bound iterm.set_bd_UNIV f g)

(* *)

proposition iApp_inject[simp]: "(iApp a b = iApp c d) = (a = c \<and> b = d)"
proof
  assume "iApp a b = iApp c d"
  then show "a = c \<and> b = d"
    unfolding iApp_def fun_eq_iff iterm.TT_inject0
      map_iterm_pre_def comp_def Abs_iterm_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
      Abs_iterm_pre_inject[OF UNIV_I UNIV_I]
    by auto
qed simp

proposition iVar_inject[simp]: "(iVar a = iVar b) = (a = b)"
  apply (rule iffI[rotated])
   apply (rule arg_cong[of _ _ iVar])
  apply assumption
  unfolding iVar_def iterm.TT_inject0 map_iterm_pre_def comp_def map_sum_def sum.case Abs_iterm_pre_inverse[OF UNIV_I]
  id_def Abs_iterm_pre_inject[OF UNIV_I UNIV_I] sum.inject
  apply (erule exE conjE)+
  apply assumption
  done

lemma iLam_inject: "(iLam xs e = iLam xs' e') = (\<exists>f. bij f \<and> |supp (f::ivar \<Rightarrow> ivar)| <o |UNIV::ivar set|
  \<and> id_on (FFVars (iLam xs e)) f \<and> dsmap f xs = xs' \<and> irrename f e = e')"
  unfolding iterm.set
  unfolding iLam_def iterm.TT_inject0 map_iterm_pre_def comp_def Abs_iterm_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_iterm_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_iterm_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_iterm_pre_def
    Un_empty_right UN_single by auto

lemma iLam_same_inject[simp]: "iLam (xs::ivar dstream) e = iLam xs e' \<longleftrightarrow> e = e'"
unfolding iLam_inject apply safe
apply(rule iterm.permute_cong_id[symmetric])
unfolding id_on_def by auto (metis bij_betw_def bij_imp_bij_betw dsnth_dsmap dtheN)

lemma bij_map_term_pre: "bij f \<Longrightarrow> |supp (f::ivar \<Rightarrow> ivar)| <o |UNIV::ivar set| \<Longrightarrow> bij (map_iterm_pre (id::ivar \<Rightarrow>ivar) f (irrename f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_iterm_pre id (inv f) (irrename (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule iterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 iterm.permute_comp0 iterm.permute_id0
  apply (rule iterm_pre.map_id0)
  apply (rule trans)
   apply (rule iterm_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 iterm.permute_comp0 iterm.permute_id0
  apply (rule iterm_pre.map_id0)
  done

lemma map_term_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::ivar \<Rightarrow> ivar)| <o |UNIV::ivar set| \<Longrightarrow>
   inv (map_iterm_pre (id::_::var_iterm_pre \<Rightarrow> _) f (irrename f) id) = map_iterm_pre id (inv f) (irrename (inv f)) id"
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
  apply assumption
  apply (rule inv_unique_comp)
   apply (rule trans)
    apply (rule iterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
   defer
  apply (rule trans)
    apply (rule iterm_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 inv_o_simp2 iterm.permute_comp0 iterm.permute_id0 iterm_pre.map_id0
   apply (rule refl)+
  done

lemma iLam_set3: "iterm_ctor v = iLam (xs::ivar dstream) e \<Longrightarrow>
 \<exists>xs' e'. iterm_ctor v = iLam xs' e' \<and> dsset xs' \<subseteq> set2_iterm_pre v \<and> e' \<in> set3_iterm_pre v"
  unfolding iLam_def iterm.TT_inject0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_iterm_pre id f (irrename f) id"])
     apply (rule bij_map_term_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding iterm.permute_id0 iterm_pre.map_id map_term_pre_inv_simp
    unfolding map_iterm_pre_def comp_def Abs_iterm_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_iterm_pre_def set3_iterm_pre_def comp_def Abs_iterm_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding iterm.FVars_permute[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF iterm.permute_bij[OF bij_imp_bij_inv supp_inv_bound]]
  iterm.permute_inv_simp[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding iterm.permute_comp[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 iterm.permute_id
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+
  by auto .

lemma iLam_avoid: "|A::ivar set| <o |UNIV::ivar set| \<Longrightarrow> \<exists>xs' e'. iLam xs e = iLam xs' e' \<and> dsset xs' \<inter> A = {}"
  apply (erule iterm.TT_fresh_cases[of _ "iLam xs e"])
   apply (drule sym)
  apply (frule iLam_set3)
  apply (erule exE conjE)+
  apply (rule exI)+
  apply (rule conjI)
   apply (rule trans)
    apply (rule sym)
    apply assumption
  apply (rotate_tac 2)
   apply assumption
  apply (drule iffD1[OF disjoint_iff])
  by auto

lemma iLam_irrename:
"bij (\<sigma>::ivar\<Rightarrow>ivar) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: ivar set| \<Longrightarrow>
 (\<And>a'. a' \<in> FFVars e - dsset (as::ivar dstream) \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> iLam as e = iLam (dsmap \<sigma> as) (irrename \<sigma> e)"
by (metis iterm.permute(3) iterm.permute_cong_id iterm.set(3))


(* Bound properties (needed as auxiliaries): *)

lemma SSupp_upd_bound:
  fixes f::"ivar \<Rightarrow> itrm"
  shows "|SSupp (f (a:=t))| <o |UNIV::ivar set| \<longleftrightarrow> |SSupp f| <o |UNIV::ivar set|"
  unfolding SSupp_def
  by (auto simp only: fun_upd_apply singl_bound ordLeq_refl split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF iterm_pre.Un_bound], rotated, of _ "{a}"]
      intro: card_of_mono1)


corollary SSupp_upd_VVr_bound[simp,intro!]: "|SSupp (VVr(a:=(t::itrm)))| <o |UNIV::ivar set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule iterm.SSupp_VVr_bound)
  done

lemma SSupp_upd_iVar_bound[simp,intro!]: "|SSupp (iVar(a:=(t::itrm)))| <o |UNIV::ivar set|"
using SSupp_upd_VVr_bound by auto

lemma supp_swap_bound[simp,intro!]: "|supp (id(x::ivar := xx, xx := x))| <o |UNIV:: ivar set|"
by (simp add: cinfinite_imp_infinite supp_swap_bound iterm.UNIV_cinfinite)

lemma SSupp_IImsupp_bound: "|SSupp \<sigma>| <o |UNIV:: ivar set| \<Longrightarrow> |IImsupp \<sigma>| <o |UNIV:: ivar set|"
unfolding IImsupp_def
by (simp add: var_ID_class.Un_bound iterm.set_bd_UNIV var_iterm_pre_class.UN_bound)

(* *)

lemma IImsupp_itvsubst_su:
assumes s[simp]: "|SSupp \<sigma>| <o  |UNIV:: ivar set|"
shows "IImsupp (itvsubst (\<sigma>::ivar\<Rightarrow>itrm) o \<tau>) \<subseteq> IImsupp \<sigma> \<union> IImsupp \<tau>"
unfolding IImsupp_def SSupp_def apply auto
by (metis s singletonD iterm.set(1) iterm.subst(1))

lemma IImsupp_itvsubst_su':
assumes s[simp]: "|SSupp \<sigma>| <o  |UNIV:: ivar set|"
shows "IImsupp (\<lambda>a. itvsubst (\<sigma>::ivar\<Rightarrow>itrm) (\<tau> a)) \<subseteq> IImsupp \<sigma> \<union> IImsupp \<tau>"
using IImsupp_itvsubst_su[OF assms] unfolding o_def .

lemma IImsupp_itvsubst_bound:
assumes s: "|SSupp \<sigma>| <o |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|IImsupp (itvsubst (\<sigma>::ivar\<Rightarrow>itrm) o \<tau>)| <o |UNIV:: ivar set|"
using IImsupp_itvsubst_su[OF s(1)] s
by (meson Un_bound SSupp_IImsupp_bound card_of_subset_bound)

lemma SSupp_itvsubst_bound:
assumes s: "|SSupp \<sigma>| <o |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|SSupp (itvsubst (\<sigma>::ivar\<Rightarrow>itrm) o \<tau>)| <o |UNIV:: ivar set|"
using IImsupp_itvsubst_bound[OF assms]
by (metis IImsupp_def card_of_subset_bound sup_ge1)

lemma SSupp_itvsubst_bound':
assumes s: "|SSupp \<sigma>| <o |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|SSupp (\<lambda>a. itvsubst (\<sigma>::ivar\<Rightarrow>itrm) (\<tau> a))| <o |UNIV:: ivar set|"
using SSupp_itvsubst_bound[OF assms] unfolding o_def .

(* *)

lemma IImsupp_irrename_su:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|"
shows "IImsupp (irrename (\<sigma>::ivar\<Rightarrow>ivar) o \<tau>) \<subseteq> imsupp \<sigma> \<union> IImsupp \<tau>"
unfolding IImsupp_def imsupp_def supp_def SSupp_def by force

lemma IImsupp_irrename_su':
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|"
shows "IImsupp (\<lambda>a. irrename (\<sigma>::ivar\<Rightarrow>ivar) (\<tau> a)) \<subseteq> imsupp \<sigma> \<union> IImsupp \<tau>"
using IImsupp_irrename_su[OF assms] unfolding o_def .

lemma IImsupp_irrename_bound:
assumes s: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|IImsupp (irrename (\<sigma>::ivar\<Rightarrow>ivar) o \<tau>)| <o |UNIV:: ivar set|"
using IImsupp_irrename_su[OF s(1,2)] s
by (meson SSupp_IImsupp_bound card_of_subset_bound imsupp_supp_bound infinite_ivar var_stream_class.Un_bound)

lemma SSupp_irrename_bound:
assumes s: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|SSupp (irrename (\<sigma>::ivar\<Rightarrow>ivar) o \<tau>)| <o |UNIV:: ivar set|"
using IImsupp_irrename_bound[OF assms]
by (metis IImsupp_def card_of_subset_bound sup_ge1)

lemma SSupp_irrename_bound':
assumes s: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o  |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "|SSupp (\<lambda>a. irrename (\<sigma>::ivar\<Rightarrow>ivar) (\<tau> a))| <o |UNIV:: ivar set|"
using SSupp_irrename_bound[OF assms] unfolding o_def .

(* *)
lemma SSupp_update_irrename_bound:
"|SSupp (iVar(\<sigma> (x::ivar) := irrename \<sigma> e))| <o |UNIV::ivar set|"
using SSupp_upd_iVar_bound .

lemma IImsupp_irrename_update_su:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "IImsupp (irrename \<sigma> \<circ> iVar(x := e)) \<subseteq>
       imsupp \<sigma> \<union> {x} \<union> FVars_iterm e"
unfolding IImsupp_def SSupp_def imsupp_def supp_def by (auto split: if_splits)

lemma IImsupp_irrename_update_bound:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "|IImsupp (irrename \<sigma> \<circ> iVar(x := e))| <o |UNIV::ivar set|"
using IImsupp_irrename_update_su[OF assms]
by (meson Un_bound card_of_subset_bound imsupp_supp_bound infinite_ivar s(2) singl_bound iterm.set_bd_UNIV)

lemma SSupp_irrename_update_bound:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "|SSupp (irrename \<sigma> \<circ> iVar(x := e))| <o |UNIV::ivar set|"
using IImsupp_irrename_update_bound[OF assms] unfolding IImsupp_def
using SSupp_irrename_bound s(1) s(2) by auto

(* Action of swapping (a particular renaming) on variables *)

lemma irrename_swap_Var1[simp]: "irrename (id(x := xx, xx := x)) (iVar (x::ivar)) = iVar xx"
apply(subst iterm.permute(1)) by auto
lemma irrename_swap_Var2[simp]: "irrename (id(x := xx, xx := x)) (iVar (xx::ivar)) = iVar x"
apply(subst iterm.permute(1)) by auto
lemma irrename_swap_Var3[simp]: "z \<notin> {x,xx} \<Longrightarrow> irrename (id(x := xx, xx := x)) (iVar (z::ivar)) = iVar z"
apply(subst iterm.permute(1)) by auto
lemma irrename_swap_Var[simp]: "irrename (id(x := xx, xx := x)) (iVar (z::ivar)) =
 iVar (if z = x then xx else if z = xx then x else z)"
apply(subst iterm.permute(1)) by auto

(* Compositionality properties of renaming and term-for-variable substitution *)

lemma itvsubst_comp:
assumes s[simp]: "|SSupp \<sigma>| <o |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "itvsubst (\<sigma>::ivar\<Rightarrow>itrm) (itvsubst \<tau> e) = itvsubst (itvsubst \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_itvsubst_bound'[OF s, simp]
  show ?thesis
  apply(induct e rule: iterm.fresh_induct[where A = "IImsupp \<sigma> \<union> IImsupp \<tau>"])
    subgoal using Un_bound[OF s]
      using var_ID_class.Un_bound SSupp_IImsupp_bound s(1) s(2) by blast
    subgoal by simp
    subgoal by simp (metis (mono_tags, lifting) comp_apply stream.map_comp stream.map_cong)
    subgoal for xs t apply(subgoal_tac "dsset xs \<inter> IImsupp (\<lambda>a. itvsubst \<sigma> (\<tau> a)) = {}")
      subgoal by simp (metis Int_Un_emptyI1 Int_Un_emptyI2 assms(1) assms(2) iterm.subst(3))
      subgoal using IImsupp_itvsubst_su'[OF s(1)] by blast . .
qed

lemma irrename_itvsubst_comp:
assumes b[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" and s[simp]: "|supp \<sigma>| <o |UNIV:: ivar set|" "|SSupp \<tau>| <o |UNIV:: ivar set|"
shows "irrename \<sigma> (itvsubst \<tau> e) = itvsubst (irrename \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_irrename_bound'[OF b s, simp]
  show ?thesis
  apply(induct e rule: iterm.fresh_induct[where A = "IImsupp \<tau> \<union> imsupp \<sigma>"])
    subgoal using s(1) s(2) Un_bound SSupp_IImsupp_bound imsupp_supp_bound infinite_ivar by blast
    subgoal by simp
    subgoal by simp (metis (mono_tags, lifting) comp_apply stream.map_comp stream.map_cong)
    subgoal for xs t apply simp apply(subgoal_tac "dsset xs \<inter> IImsupp (\<lambda>a. irrename  \<sigma> (\<tau> a)) = {}")
      subgoal by simp (metis Int_Un_emptyI1 Int_Un_emptyI2 assms(2) b iterm.map(3) iterm.subst(3) iterm_vvsubst_permute s(2))
      subgoal using IImsupp_irrename_su' b s(1) by blast . .
qed

(* Unary (term-for-var) substitution versus renaming: *)

lemma supp_SSupp_iVar_le[simp]: "SSupp (iVar \<circ> \<sigma>) = supp \<sigma>"
unfolding supp_def SSupp_def by simp

lemma irrename_eq_itvsubst_iVar:
assumes "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "irrename \<sigma> = itvsubst (iVar o \<sigma>)"
proof
  fix t
  show "irrename \<sigma> t = itvsubst (iVar o \<sigma>) t"
  proof (binder_induction t avoiding: "IImsupp (iVar \<circ> \<sigma>)" rule: iterm.strong_induct)
    case Bound
    then show ?case using SSupp_IImsupp_bound assms by (metis supp_SSupp_iVar_le)
  next
    case (iLam x1 x2)
    then show ?case using assms by (simp add: IImsupp_def disjoint_iff not_in_supp_alt dstream_map_ident_strong)
  qed (auto simp: assms intro: stream.map_cong)
qed

lemma irrename_eq_itvsubst_iVar':
"bij (\<sigma>::ivar\<Rightarrow>ivar) \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> irrename \<sigma> e = itvsubst (iVar o \<sigma>) e"
using irrename_eq_itvsubst_iVar by auto

(* Equivariance of unary substitution: *)

lemma itvsubst_irrename_comp[simp]:
assumes s[simp]: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "itvsubst (irrename \<sigma> \<circ> iVar(x := e2)) e1 = itvsubst (iVar(\<sigma> x := irrename \<sigma> e2)) (irrename \<sigma> e1)"
proof-
  note SSupp_irrename_update_bound[OF assms, unfolded comp_def, simplified, simp]
  note SSupp_update_irrename_bound[unfolded fun_upd_def, simplified, simp]
  show ?thesis
  apply(induct e1 rule: iterm.fresh_induct[where A = "{x} \<union> FFVars e2 \<union> imsupp \<sigma>"])
    subgoal by (meson Un_bound imsupp_supp_bound infinite_ivar s(2) singl_bound iterm.set_bd_UNIV)
    subgoal by auto
    subgoal apply simp by (smt (verit, best) comp_apply stream.map_comp stream.map_cong)

    subgoal for ys t apply simp apply(subgoal_tac
      "dsset ys \<inter> IImsupp ((\<lambda>a. irrename \<sigma> (if a = x then e2 else iVar a))) = {} \<and>
      \<sigma> ` dsset ys \<inter> IImsupp (\<lambda>a. if a = \<sigma> x then irrename \<sigma> e2 else iVar a) = {}")
      subgoal
        by simp (metis (no_types, lifting) Int_Un_emptyI2 dstream_map_ident_strong imsupp_empty_IntD2)
      subgoal unfolding IImsupp_def imsupp_def SSupp_def supp_def by (auto split: if_splits)  . .
qed

(* Unary substitution versus swapping: *)
lemma itvsubst_Var_irrename:
assumes xx: "xx \<notin> FFVars e1 - {x}"
shows "itvsubst (iVar((x::ivar) := e2)) e1 = itvsubst (iVar(xx := e2)) (irrename (id(x := xx, xx := x)) e1)"
proof-
  show ?thesis using xx
  apply(induct e1 rule: iterm.fresh_induct[where A = "{x,xx} \<union> FFVars e2"])
    subgoal by (metis insert_is_Un iterm.set_bd_UNIV singl_bound var_iterm_pre_class.Un_bound)
    subgoal by simp
    subgoal by simp (smt (verit, best) comp_apply stream.map_comp stream.map_cong)
    subgoal for ys t apply simp apply(subgoal_tac
      "dsset ys \<inter> IImsupp (iVar(x := e2)) = {} \<and> dsset ys \<inter> IImsupp (iVar(xx := e2)) = {}")
      subgoal
        by simp (metis SSupp_upd_iVar_bound dstream_map_ident_strong fun_upd_apply id_apply iterm.subst(3))
      subgoal unfolding IImsupp_def imsupp_def SSupp_def supp_def by auto . .
qed

(* *)

(* Swapping and unary substitution, as abbreviations: *)
abbreviation "swap t (x::ivar) y \<equiv> irrename (id(x:=y,y:=x)) t"
abbreviation "usub t (y::ivar) x \<equiv> ivvsubst (id(x:=y)) t"

(* *)

lemma usub_swap_disj:
assumes "{u,v} \<inter> {x,y} = {}"
shows "usub (swap t u v) x y = swap (usub t x y) u v"
proof-
  note iterm_vvsubst_permute[simp del]
  show ?thesis using assms
  apply(subst iterm_vvsubst_permute[symmetric]) apply auto
  apply(subst iterm.map_comp) apply auto
  apply(subst iterm_vvsubst_permute[symmetric]) apply auto
  apply(subst iterm.map_comp) apply auto
  apply(rule iterm.map_cong0)
  using iterm_pre.supp_comp_bound by auto
qed

lemma irrename_o_swap:
"irrename (id(y::ivar := yy, yy := y) o id(x := xx, xx := x)) t =
 swap (swap t x xx) y yy"
apply(subst iterm.permute_comp[symmetric])
by auto

(* *)

lemma swap_simps[simp]: "swap (iVar z) (y::ivar) x = iVar (sw z y x)"
"swap (iApp t ss) (y::ivar) x = iApp (swap t y x) (smap (\<lambda>s. swap s y x) ss)"
"swap (iLam vs t) (y::ivar) x = iLam (dsmap (\<lambda>v. sw v y x) vs) (swap t y x)"
unfolding sw_def by simp_all (metis eq_id_iff fun_upd_apply)

lemma FFVars_swap[simp]: "FFVars (swap t y x) = (\<lambda>u. sw u x y) ` (FFVars t)"
apply(subst iterm.FVars_permute) by (auto simp: sw_def)

lemma FFVars_swap'[simp]: "{x::ivar,y} \<inter> FFVars t = {} \<Longrightarrow> swap t x y = t"
apply(rule iterm.permute_cong_id) by auto

(* *)

lemma bij_betw_snth:
assumes V: "|V::ivar set| <o |UNIV::ivar set|"
shows "\<exists>f vs'. bij_betw f (dsset vs) (dsset vs') \<and> V \<inter> dsset vs' = {} \<and> dsmap f vs = vs'"
proof-
  have "|UNIV - V| =o |UNIV::ivar set|" apply(rule card_of_Un_diff_infinite)
  using V by (auto simp: infinite_ivar)
  hence "|dsset vs| <o |UNIV - V|"
    by (meson countable_card_ivar countable_card_le_natLeq ordIso_symmetric ordLess_ordIso_trans dsset_natLeq)
  then obtain f where f: "inj_on f (dsset vs)" "f ` (dsset vs) \<subseteq> UNIV - V"
  by (meson card_of_ordLeq ordLess_imp_ordLeq)
  show ?thesis apply(intro exI[of _ f] exI[of _ "dsmap f vs"])
  using f unfolding bij_betw_def by auto
qed

lemma refresh:
assumes V: "V \<inter> dsset xs = {}" "|V| <o |UNIV::ivar set|"
shows "\<exists>f xs'. bij (f::ivar\<Rightarrow>ivar) \<and> |supp f| <o |UNIV::ivar set| \<and>
               dsset xs' \<inter> dsset xs = {} \<and> dsset xs' \<inter> V = {} \<and>
               dsmap f xs = xs' \<and> id_on V f"
proof-
  have ss: "|dsset xs| <o |UNIV::ivar set|"
  by (auto simp: countable_card_ivar dsset_range V(2) var_stream_class.Un_bound)
  hence ss1: "|dsset xs \<union> V| <o |UNIV::ivar set|"
  by (meson assms(2) var_stream_class.Un_bound)
  obtain f xs' where f: "bij_betw f (dsset xs) (dsset xs')"
  "dsset xs \<inter> dsset xs' = {}" "V \<inter> dsset xs' = {}" "dsmap f xs = xs'"
  using bij_betw_snth[OF ss1, of xs] by fastforce
  hence iif: "inj_on f (dsset xs)" unfolding bij_betw_def by auto

  obtain u where u: "bij u \<and>
      |supp u| <o |UNIV::ivar set| \<and> bij_betw u (dsset xs) (dsset xs') \<and>
      imsupp u \<inter> V = {} \<and>
      eq_on (dsset xs) u f"
  using ex_bij_betw_supp_UNIV[OF _ ss f(1,2), of V] V(1) f(3)
  by (metis Int_commute infinite_ivar)
  hence iiu: "inj_on u (dsset xs)" unfolding bij_betw_def by auto

  show ?thesis apply(intro exI[of _ u] exI[of _ xs'])
  using u f iif iiu unfolding eq_on_def id_on_def imsupp_def supp_def
  apply(auto simp: dsmap_alt) by (metis dsset_range range_eqI)
qed

lemma iLam_refresh':
"\<exists>f xs'. bij f \<and> |supp f| <o |UNIV::ivar set| \<and>
      dsset xs' \<inter> dsset xs = {} \<and> dsset xs' \<inter> FFVars (iLam xs (t::itrm)) = {} \<and>
      dsmap f xs = xs' \<and>
      id_on (FFVars (iLam xs t)) f \<and>
      iLam xs t = iLam xs' (irrename f t)"
proof-
  define V where "V = FFVars (iLam xs (t::itrm))"
  have V: "V \<inter> dsset xs = {}" "|V| <o |UNIV::ivar set|"
  unfolding V_def
    using iterm.set_bd_UNIV apply (auto simp: Int_commute)
    using card_of_minus_bound by blast
  obtain f xs' where f: "bij (f::ivar\<Rightarrow>ivar) \<and> |supp f| <o |UNIV::ivar set| \<and>
               dsset xs' \<inter> dsset xs = {} \<and> dsset xs' \<inter> V = {} \<and>
               dsmap f xs = xs' \<and> id_on V f"
  using refresh[OF V] by auto
  show ?thesis apply(intro exI[of _ f] exI[of _ xs'], intro conjI)
    subgoal using f by auto
    subgoal using f by auto
    subgoal using f by auto
    subgoal using f unfolding V_def by auto
    subgoal using f by auto
    subgoal using f unfolding V_def id_on_def by auto
    subgoal unfolding iLam_inject apply(rule exI[of _ f]) using f unfolding V_def by auto .
qed

lemma iLam_refresh:
"\<exists>f xs'. bij f \<and> |supp f| <o |UNIV::ivar set| \<and>
      dsset xs' \<inter> dsset xs = {} \<and> dsset xs' \<inter> FFVars (t::itrm) = {} \<and>
      dsmap f xs = xs' \<and>
      id_on (FFVars t - dsset xs) f \<and>
      iLam xs t = iLam xs' (irrename f t)"
using iLam_refresh'[of xs t]
apply (elim exE conjE) subgoal for f xs' apply(intro exI[of _ f] exI[of _ xs'])
apply(intro conjI)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal unfolding id_on_def by (metis DiffI disjoint_iff iterm.set(3))
  subgoal by simp
  subgoal unfolding id_on_def
    using iterm.set(3) by blast
  subgoal by simp . .

(* *)

lemma FFVars_usub[simp]: "FFVars (usub t y x) =
 (if x \<in> FFVars t then FFVars t - {x} \<union> {y} else FFVars t)"
apply(subst iterm.set_map) by auto

lemma usub_simps_free[simp]: "\<And>y x. usub (iVar z) (y::ivar) x = iVar (sb z y x)"
"\<And>y x t s. usub (iApp t ss) (y::ivar) x = iApp (usub t y x) (smap (\<lambda>s. usub s y x) ss)"
by (auto simp: sb_def)

lemma usub_iLam[simp]:
"dsset vs \<inter> {x,y} = {} \<Longrightarrow> usub (iLam vs t) (y::ivar) x = iLam vs (usub t y x)"
apply(subst iterm.map)
  subgoal by auto
  subgoal by (auto simp: imsupp_def supp_def)
  subgoal by auto .

lemmas usub_simps = usub_simps_free usub_iLam

(* *)


lemma le_UNIV_insert: "|A| <o |UNIV::ivar set| \<Longrightarrow> |insert x A| <o |UNIV::ivar set|"
by (metis card_of_Un_singl_ordLess_infinite infinite_ivar insert_is_Un)

lemma irrename_usub[simp]:
assumes \<sigma>: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "irrename \<sigma> (usub t u (x::ivar)) = usub (irrename \<sigma> t) (\<sigma> u) (\<sigma> x)"
using assms
apply(induct t rule: iterm.fresh_induct[where A = "{x,u} \<union> supp \<sigma>"])
  subgoal using assms by simp (meson le_UNIV_insert)
  subgoal by (auto simp: sb_def)
  subgoal using assms apply simp unfolding stream.map_comp apply(rule stream.map_cong0) by auto
  subgoal using assms apply(subst usub_iLam) apply auto apply(subst usub_iLam) by auto .

lemma sw_sb:
"sw (sb z u x) z1 z2 = sb (sw z z1 z2) (sw u z1 z2) (sw x z1 z2)"
unfolding sb_def sw_def by auto

lemma swap_usub:
"swap (usub t (u::ivar) x) z1 z2 = usub (swap t z1 z2) (sw u z1 z2) (sw x z1 z2)"
apply(induct t rule: iterm.fresh_induct[where A = "{x,u,z1,z2}"])
  subgoal by (meson emp_bound le_UNIV_insert)
  subgoal
  apply(subst swap_simps) apply(subst usub_simps) by (auto simp: sb_def)
  subgoal apply(subst swap_simps | subst usub_simps)+
  unfolding stream.map_comp
  by (smt (verit, best) comp_apply stream.map_cong0)
  subgoal apply(subst swap_simps | subst usub_simps)+
    subgoal by auto
    subgoal apply(subst swap_simps | subst usub_simps)+
      subgoal unfolding sw_def sb_def apply simp
        by (smt (verit) dstream_map_ident_strong)
      unfolding sw_sb by presburger . .

lemma usub_refresh:
assumes "xx \<notin> FFVars t \<or> xx = x"
shows "usub t u x = usub (swap t x xx) u xx"
proof-
  note iterm_vvsubst_permute[simp del]
  show ?thesis using assms
  apply(subst iterm_vvsubst_permute[symmetric]) apply simp
    subgoal by auto
    subgoal apply(subst iterm.map_comp)
      subgoal by auto
      subgoal by auto
      subgoal apply(rule iterm.map_cong0)
      using iterm_pre.supp_comp_bound by auto . .
qed

lemma swap_commute:
"{y,yy} \<inter> {x,xx} = {} \<Longrightarrow>
 swap (swap t y yy) x xx = swap (swap t x xx) y yy"
apply(subst iterm.permute_comp)
apply auto
apply(subst iterm.permute_comp)
apply auto
apply(rule iterm.permute_cong)
by (auto simp: iterm_pre.supp_comp_bound)


(*   *)
(* Substitution from a sequence (here, a stream) *)

(* "making" the substitution function that maps each xs_i to es_i; only
meaningful if xs is non-repetitive *)
definition "imkSubst xs es \<equiv> \<lambda>x. if x \<in> dsset xs then snth es (dtheN xs x) else iVar x"

lemma imkSubst_dsnth[simp]: "imkSubst xs es (dsnth xs i) = snth es i"
unfolding imkSubst_def using dsset_range by auto

lemma imkSubst_idle[simp]: "\<not> x \<in> dsset xs \<Longrightarrow> imkSubst xs es x = iVar x"
unfolding imkSubst_def by auto

lemma card_dsset_ivar: "|dsset xs| <o |UNIV::ivar set|"
using countable_card_ivar countable_card_le_natLeq dsset_natLeq by auto

lemma SSupp_imkSubst[simp,intro]: "|SSupp (imkSubst xs es)| <o |UNIV::ivar set|"
proof-
  have "SSupp (imkSubst xs es) \<subseteq> dsset xs"
  unfolding SSupp_def by auto (metis imkSubst_idle)
  thus ?thesis by (simp add: card_of_subset_bound card_dsset_ivar)
qed

lemma imkSubst_smap_irrename:
assumes s: "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "imkSubst (dsmap \<sigma> xs) (smap (irrename \<sigma>) es2) \<circ> \<sigma> = irrename \<sigma> \<circ> imkSubst xs es2"
proof(rule ext)
  fix x
  have inj[simp]: "inj_on \<sigma> (dsset xs)"
  using s unfolding bij_def inj_on_def by auto
  show "(imkSubst (dsmap \<sigma> xs) (smap (irrename \<sigma>) es2) \<circ> \<sigma>) x = (irrename \<sigma> \<circ> imkSubst xs es2) x"
  proof(cases "x \<in> dsset xs")
    case False
    hence F: "\<not> \<sigma> x \<in> dsset (dsmap \<sigma> xs)"
    using s by auto
    thus ?thesis using F False
    unfolding o_def apply(subst imkSubst_idle)
      subgoal by auto
      subgoal using s by auto .
  next
    case True
    then obtain i where Tri: "x = dsnth xs i" by (metis dtheN)
    hence Ti: "\<sigma> x = dsnth (dsmap \<sigma> xs) i"
    using s dsmap_alt inj by blast
    thus ?thesis
    unfolding o_def Ti apply(subst imkSubst_dsnth)
    unfolding Tri by auto
  qed
qed

lemma imkSubst_smap_irrename_inv:
assumes "bij (\<sigma>::ivar\<Rightarrow>ivar)" "|supp \<sigma>| <o |UNIV::ivar set|"
shows "imkSubst (dsmap \<sigma> xs) (smap (irrename \<sigma>) es2) = irrename \<sigma> \<circ> imkSubst xs es2 o inv \<sigma>"
unfolding imkSubst_smap_irrename[OF assms, symmetric] using assms unfolding fun_eq_iff by auto

lemma card_SSupp_itvsubst_imkSubst_irrename_inv:
"bij (\<sigma>::ivar\<Rightarrow>ivar) \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow>
 |SSupp (itvsubst (irrename \<sigma> \<circ> imkSubst xs es \<circ> inv \<sigma>) \<circ> (iVar \<circ> \<sigma>))| <o |UNIV::ivar set|"
by (metis SSupp_itvsubst_bound SSupp_imkSubst imkSubst_smap_irrename_inv supp_SSupp_iVar_le)

lemma card_SSupp_imkSubst_irrename_inv:
"bij (\<sigma>::ivar\<Rightarrow>ivar) \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set|  \<Longrightarrow>
|SSupp (irrename \<sigma> \<circ> imkSubst xs es2 \<circ> inv \<sigma>)| <o |UNIV::ivar set|"
by (metis SSupp_imkSubst imkSubst_smap_irrename_inv)

lemma imkSubst_smap: "bij f \<Longrightarrow> z \<in> dsset xs \<Longrightarrow> imkSubst (dsmap f xs) es (f z) = imkSubst xs es z"
by (metis bij_betw_def bij_imp_bij_betw dsmap_alt dtheN imkSubst_dsnth)


(* *)

thm iLam_inject[no_vars]

thm ex_avoiding_bij

lemma iLam_inject_avoid:
assumes X: "|X::ivar set| <o |UNIV::ivar set|" "X \<inter> dsset xs = {}" "X \<inter> dsset xs' = {}"
shows
"(iLam xs e = iLam xs' e') =
 (\<exists>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and> id_on (FFVars (iLam xs e)) f \<and> id_on X f \<and>
      dsmap f xs = xs' \<and> irrename f e = e')"
proof
  assume "iLam xs e = iLam xs' e'"
  then obtain f where
  f: "bij f" "|supp f| <o |UNIV::ivar set|" "id_on (FFVars (iLam xs e)) f" "dsmap f xs = xs'" "irrename f e = e'"
  unfolding iLam_inject by auto
  have bf: "bij_betw f (dsset xs) (dsset xs')"
  using f unfolding bij_betw_def bij_def inj_on_def
  using dstream.set_map f by blast
  have 0: " |dsset xs \<union> dsset xs'| <o |UNIV::ivar set|"
    by (meson card_dsset_ivar var_stream_class.Un_bound)
  have 1: "(dsset xs \<union> dsset xs') \<inter> X = {}"
    by (simp add: Int_commute assms(2) assms(3) boolean_algebra.conj_disj_distrib)
  show "\<exists>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and> id_on (FFVars (iLam xs e)) f \<and> id_on X f \<and> dsmap f xs = xs' \<and> irrename f e = e'"
  using ex_avoiding_bij[OF f(2,1) infinite_ivar iterm.set_bd_UNIV f(3) 0 1 X(1)]
  apply safe subgoal for g apply(rule exI[of _ g]) using X f unfolding imsupp_def supp_def id_on_def
  apply safe
  subgoal by blast
  subgoal apply(rule dsmap_cong)
    apply (meson bij_betw_def bij_imp_bij_betw)
    apply (meson bij_betw_def bij_imp_bij_betw)
    by (smt (verit) Un_iff bf bij_betw_apply disjoint_iff_not_equal)
  subgoal apply(rule iterm.permute_cong)
    apply blast
    apply (metis supp_def)
    apply meson
    using f(2) apply force
    by (smt (verit) Diff_iff Int_emptyD UnCI bf bij_betw_iff_bijections iterm.set(3)) . .
qed(unfold iLam_inject, auto)


(* *)

lemma iLam_eq_imkSubst:
assumes il: "iLam (xs::ivar dstream) e1 = iLam xs' e1'"
shows "itvsubst (imkSubst xs es2) e1 = itvsubst (imkSubst xs' es2) e1'"
proof-
  obtain f where f: "bij f" "|supp f| <o |UNIV::ivar set|" "id_on (ILC.FFVars (iLam xs e1)) f"
  and 0: "xs' = dsmap f xs" "e1' = irrename f e1" using il[unfolded iLam_inject] by auto
  show ?thesis unfolding 0 apply(subst irrename_eq_itvsubst_iVar')
    subgoal by fact subgoal by fact
    subgoal apply(subst itvsubst_comp)
      subgoal by simp
      subgoal using f(2) by auto
      subgoal apply(rule itvsubst_cong)
        subgoal by simp
        subgoal by (simp add: SSupp_itvsubst_bound f(2))
        subgoal apply simp
     by (metis (full_types) Diff_iff dstream.set_map f(1) f(2) f(3) id_on_def
        imkSubst_idle imkSubst_smap iterm.set(3) not_imageI) . . .
qed



(* RECURSOR PREPARATIONS: *)

thm iLam_inject[no_vars]

lemma iLam_inject_strong:
assumes il: "iLam (xs::ivar dstream) e = iLam xs' e'"
and ds: "dsset xs \<inter> dsset xs' = {}"
shows "\<exists>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and>
   id_on (- (dsset xs \<union> dsset xs')) f \<and> id_on (FFVars (iLam xs e)) f \<and>
   id_on (dsset xs) (f o f) \<and>
   dsmap f xs = xs' \<and> irrename f e = e'"
proof-
  obtain f where f: "bij f" "|supp f| <o |UNIV::ivar set|"  "dsmap f xs = xs'"
  and ff: "id_on (FFVars (iLam xs e)) f" "irrename f e = e'"
  using assms unfolding iLam_inject by auto
  have bf: "bij_betw f (dsset xs) (dsset xs')"
  by (metis bij_imp_bij_betw dstream.set_map f)
  have bif: "bij_betw (inv f) (dsset xs') (dsset xs)"
  using bf bij_bij_betw_inv f by blast
  define g where "g \<equiv> \<lambda>x. if x \<in> dsset xs then f x
    else if x \<in> dsset xs' then inv f x else x"
  have sg: "supp g \<subseteq> dsset xs \<union> dsset xs'" unfolding g_def supp_def by auto
  show ?thesis apply(rule exI[of _ g]) apply safe
    subgoal unfolding bij_def apply(rule conjI)
      subgoal unfolding inj_def
        by (smt (verit, del_insts) Int_emptyD bf bij_betw_apply
         bij_implies_inject bijection.eq_invI bijection.intro ds dstream.set_map
         f g_def image_in_bij_eq)
      subgoal apply (auto simp: image_def g_def)
        apply (metis (no_types, lifting) Int_Collect Int_ac(3) Int_emptyD bf
          bij_betw_apply ds f(1) inv_simp1)
        by (metis bif bij_betw_apply f(1) inv_simp2) .
      subgoal by (meson card_dsset_ivar card_of_subset_bound sg var_stream_class.Un_bound)
      subgoal unfolding id_on_def g_def by auto
      subgoal unfolding g_def id_on_def
        by (metis f(1) ff(1) id_onD inv_simp1)
      subgoal using f bf bif unfolding g_def id_on_def fun_eq_iff
        using ds by simp (metis Int_emptyD bij_betw_apply)
      subgoal using f
        by (meson \<open>bij g\<close> \<open>|supp g| <o |UNIV|\<close> dstream.map_cong g_def)
      subgoal by (metis f ff \<open>bij g\<close> \<open>dsmap g xs = xs'\<close> \<open>id_on (FFVars (iLam xs e)) g\<close>
        \<open>|supp g| <o |UNIV|\<close> iLam_inject iLam_same_inject) .
qed


lemma iLam_inject_strong':
assumes il: "iLam (xs::ivar dstream) e = iLam xs' e'"
and zs: "dsset zs \<inter> (dsset xs \<union> dsset xs' \<union> FFVars e \<union> FFVars e') = {}"
shows
"\<exists>f f'.
   bij f \<and> |supp f| <o |UNIV::ivar set| \<and>
     id_on ((- (dsset xs \<union> dsset zs))) f \<and> id_on (FFVars (iLam xs e)) f \<and>
     id_on (dsset xs) (f o f) \<and> dsmap f xs = zs \<and>
   bij f' \<and> |supp f'| <o |UNIV::ivar set| \<and>
     id_on (- (dsset xs' \<union> dsset zs)) f' \<and> id_on (FFVars (iLam xs' e')) f' \<and>
     id_on (dsset xs') (f' o f') \<and> dsmap f' xs' = zs \<and>
   irrename f e = irrename f' e'"
proof-
  have ds: "dsset xs \<inter> dsset zs = {}" using zs by auto
  obtain f where f: "bij f" "|supp f| <o |UNIV::ivar set|"
  "dsmap f xs = zs" and bf: "bij_betw f (dsset xs) (dsset zs)"
  using ex_dsmap'[OF ds] by auto
  have bif: "bij_betw (inv f) (dsset zs) (dsset xs)"
  using bf bij_bij_betw_inv f by blast

  define g where "g \<equiv> \<lambda>x. if x \<in> dsset xs then f x
    else if x \<in> dsset zs then inv f x else x"
  have sg: "supp g \<subseteq> dsset xs \<union> dsset zs" unfolding g_def supp_def by auto

  have g: "bij g" "|supp g| <o |UNIV::ivar set|"
   "id_on (- (dsset xs \<union> dsset zs)) g" "id_on (FFVars (iLam xs e)) g"
   "id_on (dsset xs) (g o g)"
   "dsmap g xs = zs"
  subgoal unfolding bij_def apply(rule conjI)
    subgoal unfolding inj_def
    by (smt (verit, del_insts) Int_emptyD bf bij_betw_apply
         bij_implies_inject bijection.eq_invI bijection.intro ds dstream.set_map
         f g_def image_in_bij_eq)
   subgoal apply (auto simp: image_def g_def)
     apply (metis (no_types, lifting) Int_Collect Int_ac(3) Int_emptyD bf
          bij_betw_apply ds f(1) inv_simp1)
        by (metis bif bij_betw_apply f(1) inv_simp2) .
   subgoal by (meson card_dsset_ivar card_of_subset_bound sg var_stream_class.Un_bound)
   subgoal unfolding id_on_def g_def by auto
   subgoal unfolding g_def id_on_def using Int_Un_emptyI1 zs by auto
   subgoal using  zs unfolding id_on_def apply auto
     apply (metis Int_emptyD bf bij_betw_apply ds f(1) g_def inv_simp1) .
   subgoal by (metis \<open>bij g\<close> \<open>|supp g| <o |UNIV|\<close> dstream.map_cong f(1) f(2) f(3) g_def) .

  (* *)

  have ds': "dsset xs' \<inter> dsset zs = {}" using zs by auto
  obtain f' where f': "bij f'" "|supp f'| <o |UNIV::ivar set|"
  "dsmap f' xs' = zs" and bf': "bij_betw f' (dsset xs') (dsset zs)"
  using ex_dsmap'[OF ds'] by auto
  have bif: "bij_betw (inv f') (dsset zs) (dsset xs')"
  using bf' bij_bij_betw_inv f' by blast

  define g' where "g' \<equiv> \<lambda>x. if x \<in> dsset xs' then f' x
    else if x \<in> dsset zs then inv f' x else x"
  have sg: "supp g' \<subseteq> dsset xs' \<union> dsset zs" unfolding g'_def supp_def by auto

  have g': "bij g'" "|supp g'| <o |UNIV::ivar set|"
   "id_on (- (dsset xs' \<union> dsset zs)) g'" "id_on (FFVars (iLam xs' e')) g'"
   "id_on (dsset xs') (g' o g')"
   "dsmap g' xs' = zs"
  subgoal unfolding bij_def apply(rule conjI)
    subgoal unfolding inj_def
    by (smt (verit, del_insts) Int_emptyD bf' bij_betw_apply
         bij_implies_inject bijection.eq_invI bijection.intro ds' dstream.set_map
         f' g'_def image_in_bij_eq)
   subgoal apply (auto simp: image_def g'_def)
     apply (metis (no_types, lifting) Int_Collect Int_ac(3) Int_emptyD bf'
          bij_betw_apply ds' f'(1) inv_simp1)
        by (metis bif bij_betw_apply f'(1) inv_simp2) .
   subgoal by (meson card_dsset_ivar card_of_subset_bound sg var_stream_class.Un_bound)
   subgoal unfolding id_on_def g'_def by auto
   subgoal unfolding g'_def id_on_def using Int_Un_emptyI1 zs by auto
   subgoal using zs unfolding id_on_def apply auto
     apply (metis Int_emptyD bf' bij_betw_apply ds' f'(1) g'_def inv_simp1) .
   subgoal by (metis \<open>bij g'\<close> \<open>|supp g'| <o |UNIV|\<close> dstream.map_cong f'(1) f'(2) f'(3) g'_def) .

   obtain h where h: "bij h" "|supp h| <o |UNIV::ivar set|"
   and hid: "id_on (FFVars (iLam xs e)) h" "dsmap h xs = xs'" and e': "e' = irrename h e"
   using il unfolding iLam_inject by auto

   have 000: "dsmap (g' o h) xs = dsmap g xs"
     by (metis dstream.map_comp g'(1) g'(2) g'(6) g(6) h(1) h(2) hid(2))
   find_theorems dsmap dsset
   have 00: "\<And>z. z \<in> dsset xs \<Longrightarrow> g z = g' (h z)"
   using 000 using dsmap_eq2
   by (smt (verit) Int_emptyD ds dsmap.rep_eq dsnth_dsmap dsset.rep_eq dtheN g(6) o_apply)

   have 0: "irrename g e = irrename g' e'"
   unfolding e' apply(subst iterm.permute_comp)
     subgoal using h g' g by auto  subgoal using h g' g by auto
     subgoal using h g' g by auto  subgoal using h g' g by auto
     subgoal apply(rule iterm.permute_cong)
       subgoal using h g' g by auto  subgoal using h g' g by auto
       subgoal using h g' g by auto  subgoal using h g' g dstream.supp_comp_bound by blast
       subgoal for z apply auto using hid g(3,4,5) g'(3,4,5) unfolding id_on_def apply auto
       by (metis "00" Diff_iff assms(1) iterm.set(3)) . .

   show ?thesis apply(rule exI[of _ g]) apply(rule exI[of _ g'])
   using g g' 0 by auto
qed

(* *)

lemma itrm_irrename_induct[case_names iVar iApp iLam]:
assumes iiVar: "\<And>x. P (iVar (x::ivar))"
and iiApp: "\<And>e1 es2. P e1 \<Longrightarrow> (\<forall>e2\<in>sset es2. P e2) \<Longrightarrow> P (iApp e1 es2)"
and iiLam: "\<And>xs e. (\<And>f. bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> P (irrename f e)) \<Longrightarrow> P (iLam xs e)"
shows "P t"
proof-
  have "\<forall>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<longrightarrow> P (irrename f t)"
  proof(induct)
    case (iVar x)
    then show ?case using iiVar by auto
  next
    case (iApp t1 t2)
    then show ?case using iiApp by auto
  next
    case (iLam xs t)
    then show ?case using iiLam
    by simp (metis bij_o iterm.permute_comp iterm_pre.supp_comp_bound)
  qed
  thus ?thesis apply(elim allE[of _ id]) by auto
qed


(* RECURSOR *)

locale ILC_Rec =
fixes B :: "'b set"
and iVarB :: "ivar \<Rightarrow> 'b"
and iAppB :: "'b \<Rightarrow> 'b stream \<Rightarrow> 'b"
and iLamB :: "ivar dstream \<Rightarrow> 'b \<Rightarrow> 'b"
and renB :: "(ivar \<Rightarrow> ivar) \<Rightarrow> 'b \<Rightarrow> 'b"
and FVarsB :: "'b \<Rightarrow> ivar set"
assumes
(* closedness: *)
iVarB_B[simp,intro]: "\<And>x. iVarB x \<in> B"
and
iAppB_B[simp,intro]: "\<And>b1 bs2. b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> iAppB b1 bs2 \<in> B"
and
iLamB_B[simp,intro]: "\<And>xs b. b \<in>  B \<Longrightarrow> iLamB xs b \<in> B"
and
renB_B[simp]: "\<And>\<sigma> b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> b \<in> B \<Longrightarrow> renB \<sigma> b \<in> B"
and
(* proper axioms: *)
renB_id[simp,intro]: "\<And>b. b \<in> B \<Longrightarrow> renB id b = b"
and
renB_comp[simp,intro]: "\<And>b \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow>
    bij \<tau> \<Longrightarrow> |supp \<tau>| <o |UNIV::ivar set| \<Longrightarrow> b \<in> B \<Longrightarrow> renB (\<tau> o \<sigma>) b = renB \<tau> (renB \<sigma> b)"
and
renB_cong[simp]: "\<And>\<sigma> b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow>
   (\<forall>x \<in> FVarsB b. \<sigma> x = x) \<Longrightarrow>
   renB \<sigma> b = b"
(* and
NB: This is redundant:
renB_FVarsB[simp]: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow>
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b"
*)
and
(* *)
renB_iVarB[simp]: "\<And>\<sigma> x. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> renB \<sigma> (iVarB x) = iVarB (\<sigma> x)"
and
renB_iAppB[simp]: "\<And>\<sigma> b1 bs2. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow>
   b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow>
   renB \<sigma> (iAppB b1 bs2) = iAppB (renB \<sigma> b1) (smap (renB \<sigma>) bs2)"
and
renB_iLamB[simp]: "\<And>\<sigma> xs b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> b \<in> B \<Longrightarrow>
   renB \<sigma> (iLamB xs b) = iLamB (dsmap \<sigma> xs) (renB \<sigma> b)"
(* *)
and
FVarsB_iVarB: "\<And>x. FVarsB (iVarB x) \<subseteq> {x}"
and
FVarsB_iAppB: "\<And>b1 bs2. b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> FVarsB (iAppB b1 bs2) \<subseteq>
 FVarsB b1 \<union> \<Union> (FVarsB ` (sset bs2))"
and
FVarsB_iLamB: "\<And>xs b. b \<in> B \<Longrightarrow> FVarsB (iLamB xs b) \<subseteq> FVarsB b - dsset xs"
begin

lemma not_in_FVarsB_iLamB:
"b \<in> B \<Longrightarrow> dsset xs \<inter> FVarsB (iLamB xs b) = {}"
using FVarsB_iLamB by auto

thm iLam_inject_strong

lemma iLamB_inject_strong_rev:
assumes bb': "{b,b'} \<subseteq> B" and
xs': "dsset xs' \<inter> FVarsB b = {}" and
f: "bij f" "|supp f| <o |UNIV::ivar set|"
"id_on (- (dsset xs \<union> dsset xs')) f" "dsmap f xs = xs'" and r: "renB f b = b'"
shows "iLamB xs b = iLamB xs' b'"
proof-
  have id: "id_on (FVarsB (iLamB xs b)) f"
  using f FVarsB_iLamB bb' xs' unfolding id_on_def
  by blast
  have "iLamB xs b = renB f (iLamB xs b)"
  apply(rule sym) apply(rule renB_cong) using f bb' FVarsB_iLamB unfolding id_on_def
  using id unfolding id_on_def by auto
  also have "\<dots> = iLamB xs' b'" apply(subst renB_iLamB) using f r bb' by auto
  finally show ?thesis .
qed

lemma iLamB_inject_strong'_rev:
assumes bb': "{b,b'} \<subseteq> B"
and zs: "dsset zs \<inter> FVarsB b = {}" "dsset zs \<inter> FVarsB b' = {}"
and f: "bij f" "|supp f| <o |UNIV::ivar set|"
          "id_on (- (dsset xs \<union> dsset zs)) f" "dsmap f xs = zs"
and f': "bij f'" "|supp f'| <o |UNIV::ivar set|"
          "id_on (- (dsset xs' \<union> dsset zs)) f'" "dsmap f' xs' = zs"
and r: "renB f b = renB f' b'"
shows "iLamB xs b = iLamB xs' b'"
proof-
  define c where c: "c = renB f b"
  have c': "c = renB f' b'" unfolding c r ..
  have "iLamB xs b = iLamB zs c"
  apply(rule iLamB_inject_strong_rev[of _ _ _ f])
  using assms FVarsB_iLamB id_on_def unfolding c by auto
  also have "iLamB zs c = iLamB xs' b'"
  apply(rule sym, rule iLamB_inject_strong_rev[of _ _ _ f'])
  using assms FVarsB_iLamB id_on_def unfolding c by auto
  finally show ?thesis .
qed

(* NB:
We obtain a more general recursor if we replace renB_cong with iLamB_inject_strong_rev;
and an even more general one if we replace it with iLamB_inject_strong'_rev.
*)

definition morFromTrm where
"morFromTrm H \<equiv>
 (\<forall>e. H e \<in> B) \<and>
 (\<forall>x. H (iVar x) = iVarB x) \<and>
 (\<forall>e1 es2. H (iApp e1 es2) = iAppB (H e1) (smap H es2)) \<and>
 (\<forall>xs e. H (iLam xs e) = iLamB xs (H e)) \<and>
 (\<forall>\<sigma> e. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::ivar set| \<longrightarrow> H (irrename \<sigma> e) = renB \<sigma> (H e)) \<and>
 (\<forall>e. FVarsB (H e) \<subseteq> FFVars e)"

(* *)

inductive R where
iVar: "R (iVar x) (iVarB x)"
|
iApp: "R e1 b1 \<Longrightarrow> stream_all2 R es2 bs2 \<Longrightarrow> R (iApp e1 es2) (iAppB b1 bs2)"
|
iLam: "R e b \<Longrightarrow> R (iLam xs e) (iLamB xs b)"

(* *)

lemma R_iVar_elim[simp]: "R (iVar x) b \<longleftrightarrow> b = iVarB x"
apply safe
  subgoal using R.cases by fastforce
  subgoal by (auto intro: R.intros) .

lemma R_iApp_elim:
assumes "R (iApp e1 es2) b"
shows "\<exists>b1 bs2. R e1 b1 \<and> stream_all2 R es2 bs2 \<and> b = iAppB b1 bs2"
by (metis (no_types, lifting) R.cases assms iApp_inject iterm.distinct(3) iterm.distinct(6))

lemma R_iLam_elim:
assumes "R (iLam xs e) b"
shows "\<exists>xs' e' b'. R e' b' \<and> iLam xs e = iLam xs' e' \<and> b = iLamB xs' b'"
using assms by (cases rule: R.cases) auto

lemma R_total:
"\<exists>b. R e b"
proof(induct e)
  case (iVar x)
  then show ?case by (auto intro: R.intros)
next
  case (iApp e1 es2)
  then obtain b1 where r1: "R e1 b1" by auto
  from iApp obtain B where r2: "\<forall>e2 \<in> sset es2. R e2 (B e2)" by metis
  show ?case apply(rule exI[of _ "iAppB b1 (smap B es2)"])
  apply(rule R.iApp)
    subgoal by fact
    subgoal by (simp add: r2 stream_all2_iff_snth) .
next
  case (iLam x1 e)
  then show ?case by (auto intro: R.intros)
qed

lemma R_B: "R e b \<Longrightarrow> b \<in> B"
apply(induct rule: R.induct)
by simp_all (metis (no_types, lifting) iAppB_B stream_all2_iff_snth subsetI theN)

lemma R_main:
"(\<forall>b b'. R e b \<longrightarrow> R e b' \<longrightarrow> b = b') \<and>
 (\<forall>b. R e b \<longrightarrow> FVarsB b \<subseteq> FFVars e) \<and>
 (\<forall>b f. R e b \<and> bij f \<and> |supp f| <o |UNIV::ivar set|
        \<longrightarrow> R (irrename f e) (renB f b))"
proof(induct e rule: itrm_irrename_induct)
  case (iVar x)
  then show ?case using FVarsB_iVarB by auto
next
  case (iApp e1 es2)
  note iApp11 = iApp(1)[THEN conjunct1, rule_format]
  note iApp12 = iApp(1)[THEN conjunct2, THEN conjunct1, rule_format]
  note iApp13 = iApp(1)[THEN conjunct2, THEN conjunct2, rule_format,
     OF conjI, OF _ conjI]
  note iApp21 = iApp(2)[rule_format, THEN conjunct1, rule_format]
  note iApp22 = iApp(2)[rule_format, THEN conjunct2, THEN conjunct1, rule_format]
  note iApp23 = iApp(2)[rule_format, THEN conjunct2, THEN conjunct2, rule_format,
     OF _ conjI, OF _ _ conjI]

  show ?case proof safe
    fix b b' assume "R (iApp e1 es2) b" "R (iApp e1 es2) b'"
    then obtain b1 bs2 b1' bs2' where R1: "R e1 b1" "R e1 b1'"
    and R2: "stream_all2 R es2 bs2" "stream_all2 R es2 bs2'"
    and b: "b = iAppB b1 bs2" "b' = iAppB b1' bs2'"
    using R_iApp_elim by blast

    have 1: "b1 = b1'" using iApp11[OF R1] .
    have 2: "bs2 = bs2'" using iApp21 R2
    unfolding stream_all2_iff_snth sset_range image_def stream_eq_nth by fastforce
    show "b = b'" unfolding b 1 2 ..
  next
    fix b x assume "R (iApp e1 es2) b" and xx: "x \<in> FVarsB b"
    then obtain b1 bs2 where R1: "R e1 b1"
    and R2: "stream_all2 R es2 bs2"
    and b: "b = iAppB b1 bs2"
    using R_iApp_elim by blast

    have b12: "b1 \<in> B" "sset bs2 \<subseteq> B"
    using R1 R_B
    by auto (metis R2 R_B stream_all2_iff_snth theN)

    have x: "x \<in> FVarsB b1 \<or> (\<exists>b2\<in>sset bs2. x \<in> FVarsB b2)"
    using xx b12 FVarsB_iAppB unfolding b by fastforce

    have fb1: "FVarsB b1 \<subseteq> FFVars e1" using iApp12[OF R1] .
    have fb2: "\<Union> (FVarsB ` (sset bs2)) \<subseteq> \<Union> (FFVars ` (sset es2))"
    using iApp22 R2 unfolding stream_all2_iff_snth sset_range image_def by auto

    show "x \<in> FFVars (iApp e1 es2)"
    using x fb1 fb2 by auto
  next
    fix b and f::"ivar \<Rightarrow> ivar"
    assume "R (iApp e1 es2) b" and f: "bij f" "|supp f| <o |UNIV::ivar set|"
    then obtain b1 bs2 where R1: "R e1 b1"
    and R2: "stream_all2 R es2 bs2" and b: "b = iAppB b1 bs2"
    using R_iApp_elim by blast

    have b12: "b1 \<in> B" "sset bs2 \<subseteq> B"
    using R1 R_B
    by auto (metis R2 R_B stream_all2_iff_snth theN)

    have 0: "R (iApp (irrename f e1) (smap (irrename f) es2))
            (iAppB (renB f b1) (smap (renB f) bs2))"
    apply(rule R.iApp)
      subgoal using iApp13[OF R1 f] .
      subgoal using iApp23[OF _ _ f] R2
      unfolding stream_all2_iff_snth sset_range image_def by auto .

    show "R (irrename f (iApp e1 es2)) (renB f b)"
    unfolding b using 0
    using b12(1) b12(2) f(1) f(2) iterm.permute(2) renB_iAppB by auto
  qed
next
  case (iLam xs t)
  note iLamm = iLam[rule_format]
  note iLam1 = iLamm[THEN conjunct1, rule_format]
  note iLam2 = iLamm[THEN conjunct2, THEN conjunct1, rule_format]
  note iLam3 = iLamm[THEN conjunct2, THEN conjunct2, rule_format, OF _ _ conjI, OF _ _ _ conjI]
  note iLam33 = iLam3[of id, simplified]

  show ?case proof safe
    fix b1 b2 assume RiLam: "R (iLam xs t) b1" "R (iLam xs t) b2"
    then obtain xs1' t1' b1' xs2' t2' b2'
    where 1: "R t1' b1'" "iLam xs t = iLam xs1' t1'" "b1 = iLamB xs1' b1'"
    and   2: "R t2' b2'" "iLam xs t = iLam xs2' t2'" "b2 = iLamB xs2' b2'"
    using R_iLam_elim by metis

    have b12': "{b1',b2'} \<subseteq> B"
    using 1(1,3) 2(1,3) R_B by auto

    have "|dsset xs \<union> dsset xs1' \<union> dsset xs2' \<union> FFVars t \<union> FFVars t1' \<union> FFVars t2'| <o |UNIV::ivar set|"
    by (meson card_dsset_ivar iterm.set_bd_UNIV var_stream_class.Un_bound)
    then obtain zs where zs:
    "dsset zs \<inter> (dsset xs \<union> dsset xs1' \<union> dsset xs2' \<union> FFVars t \<union> FFVars t1' \<union> FFVars t2') = {}"
    by (meson iLam_avoid)

    obtain f1 f1' where
    f1: "bij f1" "|supp f1| <o |UNIV::ivar set|"
       "id_on (- (dsset xs \<union> dsset zs)) f1 \<and> id_on (FFVars(iLam xs t)) f1"
       "id_on (dsset xs) (f1 o f1)" and
    f1': "bij f1'" "|supp f1'| <o |UNIV::ivar set|"
       "id_on (- (dsset xs1' \<union> dsset zs)) f1' \<and> id_on (FFVars(iLam xs1' t1')) f1'"
       "id_on (dsset xs1') (f1' o f1')"
    and zs1: "dsmap f1 xs = zs" "dsmap f1' xs1' = zs"
    and f1f1': "irrename f1 t = irrename f1' t1'"
    using zs iLam_inject_strong'[OF 1(2), of zs] by force

    have if1': "bij (inv f1' o f1)" "|supp (inv f1' o f1)| <o |UNIV::ivar set|"
    by (auto simp add: f1 f1' iterm_pre.supp_comp_bound)

    have t1': "t1' = irrename (inv f1' o f1) t"
    using f1f1' by (metis (mono_tags, lifting) bij_imp_bij_inv f1(1,2) f1'(1,2)
       inv_o_simp1 supp_inv_bound iterm.permute_comp iterm.permute_id)

    have fvb1': "FVarsB b1' \<subseteq> FFVars t1'"
    using iLam2[OF if1', unfolded t1'[symmetric], OF 1(1)] .

    obtain f2 f2' where
    f2: "bij f2" "|supp f2| <o |UNIV::ivar set|"
       "id_on (- (dsset xs \<union> dsset zs)) f2 \<and> id_on (FFVars(iLam xs t)) f2"
       "id_on (dsset xs) (f2 o f2)" and
    f2': "bij f2'" "|supp f2'| <o |UNIV::ivar set|"
       "id_on (- (dsset xs2' \<union> dsset zs)) f2' \<and> id_on (FFVars(iLam xs2' t2')) f2'"
       "id_on (dsset xs2') (f2' o f2')"
    and zs2: "dsmap f2 xs = zs" "dsmap f2' xs2' = zs"
    and f2f2': "irrename f2 t = irrename f2' t2'"
    using zs iLam_inject_strong'[OF 2(2), of zs] by force

    have if2': "bij (inv f2' o f2)" "|supp (inv f2' o f2)| <o |UNIV::ivar set|"
    by (auto simp add: f2 f2' iterm_pre.supp_comp_bound)

    have t2': "t2' = irrename (inv f2' o f2) t"
    using f2f2'
    by (metis (mono_tags, lifting) bij_imp_bij_inv f2(1,2) f2'(1,2)
      inv_o_simp1 iterm.permute_comp iterm.permute_id supp_inv_bound)

    have fvb2': "FVarsB b2' \<subseteq> FFVars t2'"
    using iLam2[OF if2', unfolded t2'[symmetric], OF 2(1)] .

    have if2: "bij (inv f2)" "|supp (inv f2)| <o |UNIV::ivar set|"
    "bij_betw (inv f2) (dsset zs) (dsset xs)"
    apply (auto simp add: f2(1,2))
    by (metis bij_bij_betw_inv bij_imp_bij_betw dstream.set_map f2(1) f2(2) zs2(1))

    have bbe: "bij_betw f1 (dsset xs) (dsset zs)"
    "bij_betw f2' (dsset xs2') (dsset zs)"
    apply (metis bij_imp_bij_betw dstream.set_map f1(1) f1(2) zs1(1))
    by (metis bij_betw_def bij_imp_bij_betw dsset_dsmap f2'(1) zs2(2))

    have iif2: "id_on (- (dsset xs \<union> dsset zs)) (inv f2)"
    using f2(1) f2(3) id_on_inv by blast

    have eo1: "eq_on (dsset xs) f1 (inv f1)"
    using f1(4) unfolding id_on_def eq_on_def
    by simp (metis f1(1) inv_simp1)

    have eo2: "eq_on (dsset xs) f2 (inv f2)"
    using f2(4) unfolding id_on_def eq_on_def
    by simp (metis f2(1) inv_simp1)

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
       "id_on (- (dsset xs2' \<union> dsset zs)) ff2' \<and> id_on (FFVars (iLam xs2' t2')) ff2'"
    unfolding ff2'_def using f1 f2 f2'
      subgoal by auto
      subgoal unfolding ff2'_def using f1 f2 f2' by (simp add: iterm_pre.supp_comp_bound)
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
            ff2'_def if2(2) iterm.permute_comp iterm.supp_comp_bound o_inv_o_cancel t2')

    show "b1 = b2" unfolding 1(3) 2(3)
    apply(rule iLamB_inject_strong'_rev[OF b12', of zs f1' _ ff2'])
      subgoal using zs fvb1' by auto
      subgoal using zs fvb2' by auto
      subgoal using f1' by auto  subgoal using f1' by auto
      subgoal using f1' by auto  subgoal using zs1 by auto
      subgoal using ff2' by auto  subgoal using ff2' by auto
      subgoal using ff2' by auto  subgoal using zz2 by auto
      subgoal apply(rule iLam1[OF f1(1,2)])
        subgoal using iLam3[OF if1' 1(1)[unfolded t1'] f1'(1,2), unfolded rew1] .
        subgoal using iLam3[OF if2' 2(1)[unfolded t2'] ff2'(1,2), unfolded rew2] . . .

  (* *)
  next
    fix b y
    assume R: "R (iLam xs t) b" and yy: "y \<in> FVarsB b"
    then obtain xs' t' b'
    where 0: "R t' b'" "iLam xs t = iLam xs' t'" "b = iLamB xs' b'"
    using R_iLam_elim by metis

    have b': "b' \<in>  B"
    using 0(1,3) R_B by auto

    have y: "y \<notin> dsset xs'" "y \<in> FVarsB b'" using b' yy unfolding 0
    using FVarsB_iLamB[OF b'] by auto

    have "|dsset xs \<union> dsset xs' \<union> FFVars t \<union> FFVars t'| <o |UNIV::ivar set|"
    by (simp add: card_dsset_ivar iterm.set_bd_UNIV var_stream_class.Un_bound)
    then obtain z where z:
    "z \<notin> dsset xs \<union> dsset xs' \<union> FFVars t \<union> FFVars t'"
    by (meson exists_fresh)

    obtain f where
    f: "bij f" "|supp f| <o |UNIV::ivar set|"
    "id_on (FFVars (iLam xs t)) f "
    and zs: "dsmap f xs = xs'"
    and t': "t' = irrename f t"
    using 0(2) unfolding iLam_inject by auto

    have fvb't': "FVarsB b' \<subseteq> FFVars t'"
    using iLam2[OF f(1,2), unfolded t'[symmetric], OF 0(1)] .
    have yt': "y \<in> FFVars t'" using fvb't' y(2) by auto

    show "y \<in> FFVars(iLam xs t)" using yt' y unfolding 0(2) by auto

  (* *)
  next
    fix b and f :: "ivar\<Rightarrow>ivar"
    assume "R (iLam xs t) b" and f: "bij f" "|supp f| <o |UNIV::ivar set|"
    then obtain xs' t' b'
    where 0: "R t' b'" "iLam xs t = iLam xs' t'" "b = iLamB xs' b'"
    using R_iLam_elim by metis

    have b': "b' \<in>  B"
    using 0(1,3) R_B by auto

    have "|dsset xs \<union> dsset xs' \<union> FFVars t \<union> FFVars t'| <o |UNIV::ivar set|"
    by (meson card_dsset_ivar iterm.set_bd_UNIV var_stream_class.Un_bound)

    then obtain zs where zs:
    "dsset zs \<inter> (dsset xs \<union> dsset xs' \<union> FFVars t \<union> FFVars t') = {}"
    using iLam_avoid by blast

    obtain g where g: "bij g" "|supp g| <o |UNIV::ivar set|" "id_on (FFVars (iLam xs t)) g"
    and z: "dsmap g xs = xs'"
    and t': "t' = irrename g t"
    using 0(2) unfolding iLam_inject by auto

    have RR: "R (iLam (dsmap f xs') (irrename f t')) (iLamB (dsmap f xs') (renB f b'))"
    apply(rule R.iLam) unfolding t' apply(rule iLam3)
      subgoal by fact  subgoal by fact
      subgoal using 0(1) unfolding t' .
      subgoal by fact subgoal by fact .

    show "R (irrename f (iLam xs t)) (renB f b)"
    unfolding 0 using RR apply(subst iterm.permute)
      subgoal using f by auto subgoal using f by auto
      subgoal apply(subst renB_iLamB) using f b' by auto .
  qed
qed

lemmas R_functional = R_main[THEN conjunct1]
lemmas R_FFVars= R_main[THEN conjunct2, THEN conjunct1]
lemmas R_subst = R_main[THEN conjunct2, THEN conjunct2]

(* *)

definition H :: "itrm \<Rightarrow> 'b" where "H t \<equiv> SOME d. R t d"

lemma R_F: "R t (H t)"
by (simp add: R_total H_def someI_ex)

lemma ex_morFromTrm: "\<exists>H. morFromTrm H"
apply(rule exI[of _ H]) unfolding morFromTrm_def apply(intro conjI)
  subgoal using R_B R_F by auto
  subgoal using R.iVar R_F R_functional by blast
  subgoal using R.iApp R_F R_functional unfolding stream_all2_iff_snth
    by (metis snth_smap)
  subgoal using R.iLam R_F R_functional by blast
  subgoal by (meson R_F R_functional R_subst)
  subgoal by (simp add: R_F R_FFVars) .

definition rec where "rec \<equiv> SOME H. morFromTrm H"

lemma morFromTrm_rec: "morFromTrm rec"
by (metis ex_morFromTrm rec_def someI_ex)

(* *)

lemma rec_B[simp,intro!]: "rec e \<in> B"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iVar[simp]: "rec (iVar x) = iVarB x"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iApp[simp]: "rec (iApp e1 es2) = iAppB (rec e1) (smap rec es2)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iLam[simp]: "rec (iLam x e) = iLamB x (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_irrename: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow>
 rec (irrename \<sigma> e) = renB \<sigma> (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma FVarsB_rec: "FVarsB (rec e) \<subseteq> FFVars e"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_unique:
assumes "\<And>e. H e \<in> B"
"\<And>x. H (iVar x) = iVarB x"
"\<And>e1 es2. H (iApp e1 es2) = iAppB (H e1) (smap H es2)"
"\<And>xs e. H (iLam xs e) = iLamB xs (H e)"
shows "H = rec"
apply(rule ext) subgoal for e apply(induct e)
using assms by (auto cong: stream.map_cong) .

end (* context ILC_Rec *)


end
