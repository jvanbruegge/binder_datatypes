theory BMV_Fixpoint
  imports BMV_Monad
begin

type_synonym ('tv, 'v, 'btv, 'bv, 'c, 'd) FTerm_pre' =
  "'v                    \<comment>\<open>Var 'v\<close>
  + 'd * 'd              \<comment>\<open>App \<open>('tv, 'v) FTerm\<close> \<open>('tv, 'v) FTerm\<close>\<close>
  + 'd * 'tv FType       \<comment>\<open>TyApp \<open>('tv, 'v) FTerm\<close> \<open>'tv FType\<close>\<close>
  + 'bv * 'tv FType * 'c \<comment>\<open>Lam x::'v \<open>'tv FType\<close> t::\<open>('tv, 'v) FTerm\<close> binds x in t\<close>
  + 'btv * 'c            \<comment>\<open>TyLam a::'tv t::\<open>('tv, 'v) FTerm\<close> binds a in t\<close>"

ML_file \<open>../Tools/mrsbnf_comp.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 0
\<close>

local_setup \<open>fn lthy =>
let
  val T = @{typ "('tv, 'v, 'btv, 'bv, 'c, 'd) FTerm_pre'"};
  val Xs = [@{typ 'tv}, @{typ 'v}, @{typ 'btv}, @{typ 'bv}, @{typ 'c}, @{typ 'd}];

  val ((mrsbnf, (Ds, tys)), ((bmv_unfolds, (_, mrbnf_unfolds)), lthy)) = MRSBNF_Comp.mrsbnf_of_typ true (K BNF_Def.Dont_Note)
    I [] (map (apfst dest_TFree) [(@{typ 'v}, MRBNF_Def.Free_Var),
      (@{typ 'btv}, MRBNF_Def.Bound_Var), (@{typ 'bv}, MRBNF_Def.Bound_Var)])
    (fn xss => inter (op=) (flat xss) (map dest_TFree Xs))
    T
    (([], (MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds)), lthy);

  val mrsbnf = case mrsbnf of MRBNF_Util.Inl x => x | _ => error "impossible"

  val notes = [
      ("bmv_defs", bmv_unfolds)
    ] |> (map (fn (thmN, thms) =>
      ((Binding.name thmN, []), [(thms, [])])
    ));

    val (noted, lthy) = Local_Theory.notes notes lthy

  val ((mrsbnf, (tys, info)), lthy) = MRSBNF_Comp.seal_mrsbnf I (bmv_unfolds, mrbnf_unfolds)
    @{binding FTerm_pre} Xs Ds mrsbnf NONE lthy
  val (_, lthy) = MRSBNF_Def.note_mrsbnf_thms (K BNF_Def.Note_Some) I NONE mrsbnf lthy

  val bmv = MRSBNF_Def.bmv_monad_of_mrsbnf mrsbnf;
  val mrbnf = nth (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf) (BMV_Monad_Def.leader_of_bmv_monad bmv)

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
    val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy

  (* Step 4: Construct the binder fixpoint *)
  val (fp_res, lthy) = MRBNF_FP.construct_binder_fp BNF_Util.Least_FP
  [{
    FVars = [SOME "FTVars", SOME "FVars"],
    T_name = "FTerm",
    nrecs = 2,
    permute = NONE,
    pre_mrbnf = mrbnf
  }] [[([], [0])], [([], [0])]] lthy

  (* Step 5: Define recursor locales *)  
  val (recursor_result, lthy) = MRBNF_Recursor.create_binding_recursor I fp_res lthy;

  (*val ([(rec_mrbnf, vvsubst_res)], lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint [@{binding vvsubst_FTerm}]
    I fp_res (#QREC_fixed recursor_result) lthy;
  val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (hd (#quotient_fps fp_res))))) rec_mrbnf lthy;
  *)
in lthy end
\<close>
print_theorems

(* Substitution axioms *)
abbreviation \<eta> :: "'v::var \<Rightarrow> ('tv::var, 'v::var, 'a::var, 'b::var, 'c, 'd) FTerm_pre" where
  "\<eta> a \<equiv> Abs_FTerm_pre (Inl a)"

lemma eta_free: "set2_FTerm_pre (\<eta> a) = {a}"
  apply (unfold set2_FTerm_pre_def sum.set_map UN_empty2 Un_empty_left Un_empty_right prod.set_map comp_def
    Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_empty UN_single
  )
  apply (rule refl)
  done
lemma eta_inj: "\<eta> a = \<eta> b \<Longrightarrow> a = b"
  apply (unfold Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] sum.inject)
  apply assumption
  done
lemma eta_natural:
  fixes f1::"'x1::var \<Rightarrow> 'x1" and f2::"'x2::var \<Rightarrow> 'x2" and f3::"'x3::var \<Rightarrow> 'x3" and f4::"'x4::var \<Rightarrow> 'x4"
  assumes "|supp f1| <o |UNIV::'x1 set|" "|supp f2| <o |UNIV::'x2 set|"
    "bij f3" "|supp f3| <o |UNIV::'x3 set|" "bij f4" "|supp f4| <o |UNIV::'x4 set|"
  shows "map_FTerm_pre f1 f2 f3 f4 f5 f6 \<circ> \<eta> = \<eta> \<circ> f2"
  apply (rule ext)
  apply (unfold comp_def map_FTerm_pre_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps)
  apply (rule refl)
  done

(* Construction of substitution *)
definition VVr :: "'v::var \<Rightarrow> ('tv::var, 'v) FTerm" where
  "VVr \<equiv> FTerm_ctor \<circ> \<eta>"
definition isVVr :: "('tv::var, 'v::var) FTerm \<Rightarrow> bool" where
  "isVVr x \<equiv> \<exists>a. x = VVr a"
definition asVVr :: "('tv::var, 'v::var) FTerm \<Rightarrow> 'v" where
  "asVVr x \<equiv> (if isVVr x then SOME a. x = VVr a else undefined)"

abbreviation "IImsupp_FTerm1 \<equiv> IImsupp VVr FTVars"
abbreviation "IImsupp_FTerm2 f \<equiv> SSupp VVr f \<union> IImsupp VVr FVars f"

lemma asVVr_VVr: "asVVr (VVr a) = a"
  apply (unfold asVVr_def isVVr_def)
  apply (subst if_P)
   apply (rule exI)
   apply (rule refl)
  apply (rule someI2)
   apply (rule refl)
  apply (unfold VVr_def comp_def)
  apply (unfold FTerm.TT_inject0)
  apply (erule exE conjE)+
  apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I]
    map_sum.simps Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] id_apply
    sum.inject
  )
  apply (erule sym)
  done

lemma permute_VVr:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "permute_FTerm f1 f2 (VVr a) = VVr (f2 a)"
  apply (unfold VVr_def comp_def)
  apply (rule trans)
   apply (rule FTerm.permute_ctor[OF assms])
  apply (subst fun_cong[OF eta_natural, unfolded comp_def])
      apply (rule assms)+
  apply (rule refl)
  done

lemma isVVr_permute:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "isVVr (permute_FTerm f1 f2 x) = isVVr x"
  apply (unfold isVVr_def)
  apply (rule iffI)
   apply (erule exE)
   apply (drule arg_cong[of _ _ "permute_FTerm (inv f1) (inv f2)"])
   apply (subst (asm) FTerm.permute_comp)
           apply (rule assms bij_imp_bij_inv supp_inv_bound)+
   apply (subst (asm) inv_o_simp1, rule assms)+
   apply (unfold FTerm.permute_id)
   apply hypsubst_thin
   apply (subst permute_VVr)
       apply (rule assms bij_imp_bij_inv supp_inv_bound)+
   apply (rule exI)
   apply (rule refl)
  apply (erule exE)
  apply hypsubst_thin
  apply (subst permute_VVr)
      apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (rule exI)
  apply (rule refl)
  done

lemma IImsupp_VVrs: "f2 a \<noteq> a \<Longrightarrow> imsupp f2 \<inter> IImsupp_FTerm2 y = {} \<Longrightarrow> y a = VVr a"
  apply (unfold imsupp_def supp_def SSupp_def)
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply (rule UnI1)
   apply (erule iffD2[OF mem_Collect_eq])
  apply (unfold Un_iff de_Morgan_disj mem_Collect_eq not_not)
  apply (erule conjE)
  apply assumption
  done

lemma IImsupp_permute_commute:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp f1 \<inter> IImsupp_FTerm1 y = {} \<Longrightarrow> imsupp f2 \<inter> IImsupp_FTerm2 y = {} \<Longrightarrow> permute_FTerm f1 f2 \<circ> y = y \<circ> f2"
  apply (rule ext)
  apply (unfold comp_def)
  subgoal for a
    apply (rule case_split[of "f2 a = a"])
     apply (rule case_split[of "y a = VVr a"])
      apply (rule trans)
       apply (rule arg_cong[of _ _ "permute_FTerm f1 f2"])
       apply assumption
      apply (rule trans)
       apply (rule permute_VVr)
          apply (rule assms)+
      apply (rule trans)
       apply (rule arg_cong[of _ _ VVr])
       apply assumption
      apply (rule sym)
      apply (rotate_tac -2)
      apply (erule subst[OF sym])
      apply assumption

     apply (rule trans)
      apply (rule FTerm.permute_cong_id)
           apply (rule assms)+
      (* REPEAT_DETERM *)
       apply (erule id_onD[rotated])
       apply (rule imsupp_id_on)
       apply (erule Int_subset_empty2)
       apply (unfold SSupp_def IImsupp_def)[1]
       apply (rule subsetI)
       apply (rule UnI2)?
       apply (rule UN_I[rotated])
        apply assumption
       apply (rule CollectI)
       apply assumption
      (* repeated *)
      (* REPEAT_DETERM *)
      apply (erule id_onD[rotated])
      apply (rule imsupp_id_on)
      apply (erule Int_subset_empty2)
       apply (unfold SSupp_def IImsupp_def)[1]
      apply (rule subsetI)
      apply (rule UnI2)?
      apply (rule UN_I[rotated])
       apply assumption
      apply (rule CollectI)
      apply assumption
      (* END REPEAT_DETERM *)
     apply (rotate_tac -2)
     apply (erule subst[OF sym])
     apply (rule refl)

    apply (rule trans)
     apply (rule arg_cong[of _ _ "permute_FTerm f1 f2"])
     defer
     apply (rule trans)
      prefer 3
      apply (erule IImsupp_VVrs)
      apply assumption
     apply (rule permute_VVr)
        apply (rule f_prems)+
    apply (rule sym)
    apply (rule IImsupp_VVrs)
     apply (erule bij_not_eq_twice[rotated])
     apply (rule f_prems)
    apply assumption
    done
  done

type_synonym ('tv, 'v) U1_pre = "('tv, 'v, 'tv, 'v, ('tv, 'v) FTerm, ('tv, 'v) FTerm) FTerm_pre"

lemmas eta_natural' = fun_cong[OF eta_natural, unfolded comp_def]

lemma eta_set_empties:
  fixes a::"'v::var"
  shows
    "set1_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set3_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set4_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set5_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set6_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
      apply -
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF exists_fresh, of "set1_FTerm_pre (\<eta> a)"])
      apply (rule FTerm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set1_FTerm_pre])
      prefer 2
      apply (subst (asm) FTerm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural, unfolded comp_def])
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF exists_fresh, of "set3_FTerm_pre (\<eta> a)"])
      apply (rule FTerm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set3_FTerm_pre])
      prefer 2
      apply (subst (asm) FTerm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural, unfolded comp_def])
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF exists_fresh, of "set4_FTerm_pre (\<eta> a)"])
      apply (rule FTerm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set4_FTerm_pre])
      prefer 2
      apply (subst (asm) FTerm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule eta_natural')
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (drule image_const)
     apply (drule iffD1[OF all_cong1, rotated])
      apply (rule sym)
      apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
      apply (rule FTerm_pre.set_map)
           apply (rule supp_id_bound bij_id)+
     apply (subst (asm) eta_natural')
         apply (rule supp_id_bound bij_id)+
     apply (unfold id_def)
     apply (drule forall_in_eq_UNIV)
     apply (drule trans[symmetric])
      apply (rule conjunct1[OF card_order_on_Card_order, OF FTerm_pre.bd_card_order])
     apply (drule card_of_ordIso_subst)
     apply (drule ordIso_symmetric)
     apply (drule ordIso_transitive)
      apply (rule ordIso_symmetric)
      apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
      apply (rule conjunct2[OF card_order_on_Card_order, OF FTerm_pre.bd_card_order])
     apply (erule ordIso_ordLess_False)
     apply (rule FTerm_pre.set_bd)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (drule image_const)
     apply (drule iffD1[OF all_cong1, rotated])
      apply (rule sym)
      apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
      apply (rule FTerm_pre.set_map)
           apply (rule supp_id_bound bij_id)+
     apply (subst (asm) eta_natural')
         apply (rule supp_id_bound bij_id)+
     apply (unfold id_def)
     apply (drule forall_in_eq_UNIV)
     apply (drule trans[symmetric])
      apply (rule conjunct1[OF card_order_on_Card_order, OF FTerm_pre.bd_card_order])
     apply (drule card_of_ordIso_subst)
     apply (drule ordIso_symmetric)
     apply (drule ordIso_transitive)
      apply (rule ordIso_symmetric)
      apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
      apply (rule conjunct2[OF card_order_on_Card_order, OF FTerm_pre.bd_card_order])
     apply (erule ordIso_ordLess_False)
     apply (rule FTerm_pre.set_bd)
    apply (erule FalseE)
    done
  done

lemmas Cinfinite_UNIV = conjI[OF FTerm_pre.UNIV_cinfinite card_of_Card_order]
lemmas Cinfinite_card = cmin_Cinfinite[OF Cinfinite_UNIV Cinfinite_UNIV]
lemmas regularCard_card = cmin_regularCard[OF FTerm_pre.var_regular FTerm_pre.var_regular Cinfinite_UNIV Cinfinite_UNIV]
lemmas Un_bound = regularCard_Un[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]
lemmas UN_bound = regularCard_UNION[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]

context
  fixes f1::"'var::var \<Rightarrow> ('tyvar::var, 'var) FTerm" and f2::"'tyvar \<Rightarrow> 'tyvar FType"
  assumes f_prems: "|SSupp VVr f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
    "|SSupp TyVar f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
begin

interpretation tvsubst: QREC_cmin_fixed_FTerm "IImsupp_FTerm1 f1 \<union> (SSupp TyVar f2 \<union> IImsupp TyVar FVars_FType f2)"
  "IImsupp_FTerm2 f1" "\<lambda>y. if isVVr (FTerm_ctor (map_FTerm_pre id id id id fst fst y)) then
    f1 (asVVr (FTerm_ctor (map_FTerm_pre id id id id fst fst y)))
  else FTerm_ctor (Sb_FTerm_pre id f2 (map_FTerm_pre id id id id snd snd y))"
  apply unfold_locales

      apply (((unfold IImsupp_def)[1]), (rule Un_bound UN_bound f_prems card_of_Card_order FTerm.FVars_bd_UNIVs FType.FVars_bd_UNIVs cmin_greater
        var_class.UN_bound f_prems[THEN ordLess_ordLeq_trans] cmin1 cmin2
        )+)+

  subgoal for g1 g2 y
    apply (subst FTerm_pre.map_comp, (assumption | erule ordLess_ordLeq_trans[OF _ cmin1] ordLess_ordLeq_trans[OF _ cmin2] | rule card_of_Card_order supp_id_bound bij_id)+)+
    apply (unfold Product_Type.snd_comp_map_prod Product_Type.fst_comp_map_prod id_o_commute[of g1] id_o_commute[of g2])
    apply (subst FTerm_pre.map_comp[symmetric], (assumption | erule ordLess_ordLeq_trans[OF _ cmin1] ordLess_ordLeq_trans[OF _ cmin2] | rule card_of_Card_order supp_id_bound bij_id)+)+
    apply (subst FTerm.permute_ctor[symmetric] isVVr_permute, (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+

    apply (rule case_split)
     apply (subst if_P)
      apply assumption
     apply (unfold if_P if_not_P)
     apply (unfold isVVr_def)[1]
     apply (erule exE)
    apply (rotate_tac -1)
     apply (erule subst[OF sym])
     apply (subst permute_VVr)
    apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
     apply (unfold asVVr_VVr)
     apply (rule IImsupp_permute_commute[THEN fun_cong, unfolded comp_def])
          apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
      apply (erule Int_subset_empty2)
      apply (rule subsetI)
      apply (assumption | erule UnI1 UnI2 | rule UnI1)+

    apply (rule trans)
    apply (rule FTerm.permute_ctor)
        apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+

    apply (subst trans[OF comp_apply[symmetric] FTerm_pre.map_Sb_strong(1)[THEN fun_cong]])
          apply (assumption | erule ordLess_ordLeq_trans[OF _ cmin1] ordLess_ordLeq_trans[OF _ cmin2]
          | rule card_of_Card_order supp_id_bound bij_id f_prems[THEN ordLess_ordLeq_trans, OF cmin1] f_prems[THEN ordLess_ordLeq_trans, OF cmin2])+
    apply (unfold0 id_o o_id inv_o_simp2 comp_apply)
    apply (rule arg_cong[of _ _ FTerm_ctor])
    apply (rule FTerm_pre.Sb_cong)
         apply (assumption  | erule ordLess_ordLeq_trans[OF _ cmin1] ordLess_ordLeq_trans[OF _ cmin2]
        | rule supp_id_bound card_of_Card_order supp_inv_bound SSupp_comp_bound infinite_UNIV FType.SSupp_map_bound
          f_prems[THEN ordLess_ordLeq_trans, OF cmin1] f_prems[THEN ordLess_ordLeq_trans, OF cmin2]
        | (unfold comp_assoc)[1])+
     apply (rule refl)
    apply (subst (asm) FTerm_pre.map_comp, (assumption | erule ordLess_ordLeq_trans[OF _ cmin1] ordLess_ordLeq_trans[OF _ cmin2] | rule card_of_Card_order supp_id_bound bij_id)+)
    apply (unfold id_o o_id FTerm_pre.set_Vrs(1)[symmetric])
    apply (subst (asm) FTerm_pre.set_map, (assumption | erule ordLess_ordLeq_trans[OF _ cmin1] ordLess_ordLeq_trans[OF _ cmin2] | rule card_of_Card_order supp_id_bound bij_id)+)
    apply (erule imageE)
    apply hypsubst
    apply (rule trans[OF comp_apply])
    apply (unfold inv_simp1)
    apply (rule trans[OF comp_apply])
    apply (subst FType.vvsubst_permute, (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)
    apply (rule FType.IImsupp_permute_commute[THEN fun_cong, unfolded comp_def])
      apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
    apply (erule Int_subset_empty2)
    apply (rule subsetI)
    apply (rule UnI2)
    apply (unfold IImsupp_FType_def comp_def SSupp_FType_def tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def
      IImsupp_def SSupp_def VVr_def TyVar_def
    )[1]
    apply assumption
    done

  subgoal premises prems
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
    apply (unfold if_not_P)
     apply (unfold isVVr_def)[1]
     apply (erule exE)
     apply (erule subst[OF sym])
     apply (unfold asVVr_VVr)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FTVars])
       apply assumption
      apply (rule Un_upper1)
    apply (rule subsetI)
     apply (rule UnI2)
     apply (rule UnI1)
     apply (unfold IImsupp_def SSupp_def)[1]
     apply (rule UN_I)
      apply (rule CollectI)
      apply assumption
     apply assumption

    apply (erule thin_rl)
    apply (subst FTerm_pre.map_Sb[THEN fun_cong, unfolded comp_def, symmetric])
         apply (rule supp_id_bound bij_id f_prems[THEN ordLess_ordLeq_trans, OF cmin1] f_prems[THEN ordLess_ordLeq_trans, OF cmin2] card_of_Card_order)+
    apply (unfold FTerm.FVars_ctor)
    apply (subst FTerm_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id image_comp[unfolded comp_def])
    apply (subst FTerm_pre.set_Sb, (rule supp_id_bound bij_id f_prems[THEN ordLess_ordLeq_trans, OF cmin1] f_prems[THEN ordLess_ordLeq_trans, OF cmin2] card_of_Card_order)+)+
    apply (rule Un_mono')+

      apply (unfold FTerm_pre.set_Vrs(1))[1]
      apply (subst FTerm_pre.Vrs_Sb, (rule supp_id_bound bij_id f_prems[THEN ordLess_ordLeq_trans, OF cmin1] f_prems[THEN ordLess_ordLeq_trans, OF cmin2] card_of_Card_order)+)
      apply (rule subsetI)
      apply (erule UN_E)
      apply (rule case_split[of "_ = _", rotated])
       apply (unfold IImsupp_def SSupp_def)[1]
       apply (rule UnI2)+
       apply (rule UN_I)
        apply (rule CollectI)
        apply assumption
       apply assumption
      apply (rule UnI1)
      apply (rotate_tac -2)
      apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
       apply (erule arg_cong)
      apply (unfold FType.Vrs_Inj)
      apply (drule singletonD)
      apply hypsubst
      apply assumption

     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule Diff_Un_disjunct)
      apply (rule prems)
     apply (rule Diff_mono[OF _ subset_refl])
     apply (unfold UN_extend_simps(2))
    (* REPEAT_DETERM *)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* repeated *)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* END REPEAT_DETERM *)
    done


  subgoal premises prems
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
    apply (unfold if_not_P)
     apply (unfold isVVr_def)[1]
     apply (erule exE)
     apply (erule subst[OF sym])
     apply (unfold asVVr_VVr)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FVars])
       apply assumption
      apply (rule Un_upper1)
    apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold IImsupp_def SSupp_def)[1]
    apply (rule UnI2)
     apply (rule UN_I)
      apply (rule CollectI)
      apply assumption
     apply assumption

    apply (erule thin_rl)
    apply (subst FTerm_pre.map_Sb[THEN fun_cong, unfolded comp_def, symmetric])
         apply (rule supp_id_bound bij_id f_prems[THEN ordLess_ordLeq_trans, OF cmin1] f_prems[THEN ordLess_ordLeq_trans, OF cmin2] card_of_Card_order)+
    apply (unfold FTerm.FVars_ctor)
    apply (subst FTerm_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id image_comp[unfolded comp_def])
    apply (subst FTerm_pre.set_Sb, (rule supp_id_bound bij_id f_prems[THEN ordLess_ordLeq_trans, OF cmin1] f_prems[THEN ordLess_ordLeq_trans, OF cmin2] card_of_Card_order)+)+
    apply (rule Un_mono')+

      apply (unfold FTerm_pre.set_Vrs(2))[1]
      apply (subst FTerm_pre.Vrs_Sb, (rule supp_id_bound bij_id f_prems[THEN ordLess_ordLeq_trans, OF cmin1] f_prems[THEN ordLess_ordLeq_trans, OF cmin2] card_of_Card_order)+)
      apply (unfold image_id)
      apply (rule Un_upper1)

     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule Diff_Un_disjunct)
      apply (rule prems)
     apply (rule Diff_mono[OF _ subset_refl])
     apply (unfold UN_extend_simps(2))
    (* REPEAT_DETERM *)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* repeated *)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* END REPEAT_DETERM *)
    done
  done

definition "tvsubst_FTerm = tvsubst.REC_FTerm"

lemma tvsubst_VVr: "tvsubst_FTerm (VVr a) = f1 a"
  apply (unfold VVr_def comp_def)
  apply (unfold tvsubst_FTerm_def)
  apply (rule trans)
   apply (rule tvsubst.REC_ctor)
     apply (unfold eta_set_empties noclash_FTerm_def)
     apply (rule Int_empty_left conjI)+
  apply (subst FTerm_pre.map_comp, (rule supp_id_bound bij_id)+)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric] FTerm_pre.map_id
      VVr_def[THEN meta_eq_to_obj_eq, THEN fun_cong, unfolded comp_def, symmetric] asVVr_VVr
      )
  apply (subst if_P)
   apply (unfold isVVr_def)
   apply (rule exI)
   apply (rule refl)
  apply (rule refl)
  done

lemma tvsubst_not_is_VVr:
  assumes empty_prems: "set3_FTerm_pre x \<inter> (IImsupp_FTerm1 f1 \<union> (SSupp TyVar f2 \<union> IImsupp TyVar FVars_FType f2)) = {}" "set4_FTerm_pre x \<inter> IImsupp_FTerm2 f1 = {}"
  and noclash: "noclash_FTerm x"
  and VVr_prems: "\<not>isVVr (FTerm_ctor x)"
  shows "tvsubst_FTerm (FTerm_ctor x) = FTerm_ctor (Sb_FTerm_pre id f2 (map_FTerm_pre id id id id tvsubst_FTerm tvsubst_FTerm x))"
  apply (unfold tvsubst_FTerm_def)
  apply (rule trans)
   apply (rule tvsubst.REC_ctor)
     apply (rule assms)+
  apply (subst FTerm_pre.map_comp, (rule supp_id_bound bij_id)+)+
  apply (unfold id_o o_id comp_def[of fst] comp_def[of snd] snd_conv fst_conv id_def[symmetric] FTerm_pre.map_id)
  apply (rule if_not_P)
  apply (rule assms)
  done
end

pbmv_monad "('tv, 'v) FTerm" and "'tv FType"
  Sbs: tvsubst_FTerm
  Injs: VVr TyVar
  Vrs: FVars FTVars
  bd: natLeq
            apply (rule infinite_regular_card_order_natLeq)

           apply (rule ext)
           apply (rule trans[rotated])
            apply (rule id_apply[symmetric])
  subgoal for x
    apply (rule FTerm.TT_fresh_induct[OF emp_bound emp_bound, of _ x])
    subgoal for x
      apply (rule case_split[of "isVVr (FTerm_ctor x)"])
       apply (unfold isVVr_def)[1]
       apply (erule exE)
       apply (rotate_tac -1)
       apply (erule subst[OF sym])
       apply (rule tvsubst_VVr)
        apply (rule SSupp_Inj_bound cmin_greater card_of_Card_order)+
      apply (rule trans)
      apply (rule tvsubst_not_is_VVr)
            apply (rule SSupp_Inj_bound cmin_greater card_of_Card_order)+
          apply (unfold IImsupp_def SSupp_Inj UN_empty Un_empty_left Un_empty_right noclash_FTerm_def)[3]
          apply (rule Int_empty_right)+
        apply assumption+
      apply (subst FTerm_pre.map_cong0)
                      apply (assumption | rule supp_id_bound bij_id refl)+
      apply (unfold id_def[symmetric] FTerm_pre.map_id FTerm_pre.Sb_Inj)
      apply (unfold id_def)
      apply (rule refl)
      done
    done

          apply (rule ext)
          apply (rule trans[OF comp_apply])
          apply (rule tvsubst_VVr)
            apply (assumption | rule cmin_greater card_of_Card_order)+
  oops

(* Sugar theorems for substitution *)
definition Var :: "'v \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "Var a \<equiv> FTerm_ctor (Abs_FTerm_pre (Inl a))"
definition App :: "('tv, 'v) FTerm \<Rightarrow> ('tv, 'v) FTerm \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "App t1 t2 \<equiv> FTerm_ctor (Abs_FTerm_pre (Inr (Inl (t1, t2))))"
definition TyApp :: "('tv, 'v) FTerm \<Rightarrow> 'tv FType \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "TyApp t T \<equiv> FTerm_ctor (Abs_FTerm_pre (Inr (Inr (Inl (t, T)))))"
definition Lam :: "'v \<Rightarrow> 'tv FType \<Rightarrow> ('tv, 'v) FTerm \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "Lam x T t \<equiv> FTerm_ctor (Abs_FTerm_pre (Inr (Inr (Inr (Inl (x, T, t))))))"
definition TyLam :: "'tv \<Rightarrow> ('tv, 'v) FTerm \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "TyLam a t \<equiv> FTerm_ctor (Abs_FTerm_pre (Inr (Inr (Inr (Inr (a, t))))))"

lemma FTerm_subst:
  fixes f1::"'v \<Rightarrow> ('tv::var, 'v::var) FTerm" and f2::"'tv \<Rightarrow> 'tv FType"
  assumes "|SSupp VVr f1| <o cmin |UNIV::'tv set| |UNIV::'v set|" "|SSupp TyVar f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows
    "tvsubst_FTerm f1 f2 (Var x) = f1 x"
    "tvsubst_FTerm f1 f2 (App t1 t2) = App (tvsubst_FTerm f1 f2 t1) (tvsubst_FTerm f1 f2 t2)"
    "tvsubst_FTerm f1 f2 (TyApp t T) = TyApp (tvsubst_FTerm f1 f2 t) (tvsubst_FType f2 T)"
    "x \<notin> IImsupp_FTerm2 f1 \<Longrightarrow> tvsubst_FTerm f1 f2 (Lam x T t) = Lam x (tvsubst_FType f2 T) (tvsubst_FTerm f1 f2 t)"
    "a \<notin> IImsupp_FTerm1 f1 \<union> (SSupp TyVar f2 \<union> IImsupp TyVar FVars_FType f2) \<Longrightarrow> tvsubst_FTerm f1 f2 (TyLam a t) = TyLam a (tvsubst_FTerm f1 f2 t)"
      apply (unfold Var_def App_def TyApp_def Lam_def TyLam_def)
      apply (unfold meta_eq_to_obj_eq[OF VVr_def, THEN fun_cong, unfolded comp_def, symmetric])
      apply (rule tvsubst_VVr)
       apply (rule assms)+

     apply (rule trans)
      apply (rule tvsubst_not_is_VVr)
           apply (rule assms)+
         apply (unfold set3_FTerm_pre_def sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right UN_singleton comp_def
      Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_single UN_empty set4_FTerm_pre_def noclash_FTerm_def
      )
         apply (rule Int_empty_left conjI)+
      apply (unfold isVVr_def VVr_def comp_def FTerm.TT_inject0)[1]
      apply (rule notI)
      apply (erule exE conjE)+
      apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I]
      )[1]
      apply (rotate_tac -1)
      apply (erule contrapos_pp)
      apply (rule sum.distinct)
     apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] Sb_FTerm_pre_def id_def map_prod_simp
      )[1]
     apply (rule refl)

    apply (rule trans)
     apply (rule tvsubst_not_is_VVr)
          apply (rule assms)+
        apply (unfold set3_FTerm_pre_def sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right UN_singleton comp_def
      Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_single UN_empty set4_FTerm_pre_def noclash_FTerm_def
      )
        apply (rule Int_empty_left conjI)+
     apply (unfold isVVr_def VVr_def comp_def FTerm.TT_inject0)[1]
     apply (rule notI)
     apply (erule exE conjE)+
     apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I]
      )[1]
     apply (rotate_tac -1)
     apply (erule contrapos_pp)
     apply (rule sum.distinct)
    apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] Sb_FTerm_pre_def id_def map_prod_simp bmv_defs
      )[1]
    apply (unfold id_def[symmetric] FType.map_id)
    apply (rule refl)

   apply (rule trans)
    apply (rule tvsubst_not_is_VVr)
         apply (rule assms)+
       apply (unfold set2_FTerm_pre_def set6_FTerm_pre_def set3_FTerm_pre_def sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right UN_singleton comp_def
      Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_single UN_empty set4_FTerm_pre_def noclash_FTerm_def prod_set_simps
      )
       apply (rule Int_empty_left Int_empty_right conjI iffD2[OF disjoint_single] | assumption)+
    apply (unfold isVVr_def VVr_def comp_def FTerm.TT_inject0)[1]
    apply (rule notI)
    apply (erule exE conjE)+
    apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I]
      )[1]
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (rule sum.distinct)
   apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] Sb_FTerm_pre_def id_def map_prod_simp bmv_defs
      )[1]
   apply (unfold id_def[symmetric] FType.map_id)
   apply (rule refl)

  apply (rule trans)
   apply (rule tvsubst_not_is_VVr)
        apply (rule assms)+
      apply (unfold set2_FTerm_pre_def set6_FTerm_pre_def set3_FTerm_pre_def sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right UN_singleton comp_def
      Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_single UN_empty set4_FTerm_pre_def noclash_FTerm_def prod_set_simps
      set1_FTerm_pre_def
      )
      apply (rule Int_empty_left Int_empty_right conjI iffD2[OF disjoint_single] | assumption)+
   apply (unfold isVVr_def VVr_def comp_def FTerm.TT_inject0)[1]
   apply (rule notI)
   apply (erule exE conjE)+
   apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I]
      )[1]
   apply (rotate_tac -1)
   apply (erule contrapos_pp)
   apply (rule sum.distinct)
  apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] Sb_FTerm_pre_def id_def map_prod_simp bmv_defs
      )[1]
  apply (rule refl)
  done

end