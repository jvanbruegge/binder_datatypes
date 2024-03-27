theory Sugar
  imports Fixpoint
begin

ML \<open>
val res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Fixpoint.T1")
\<close>

ML_file \<open>../Tools/mrbnf_vvsubst.ML\<close>

local_setup \<open>fn lthy =>
let
  val (ress, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint
    [@{binding vvsubst_T1}, @{binding vvsubst_T2}] I res lthy;
  val lthy = @{fold 2} (fn (mrbnf, _) => fn quot =>
    MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T quot))) mrbnf
  ) ress (#quotient_fps res) lthy;
in lthy end
\<close>
print_theorems
print_mrbnfs

class var = var_T1_pre + var_T2_pre

definition Var_T1 :: "'var \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T1" where
  "Var_T1 x \<equiv> T1_ctor (Abs_T1_pre (Inl (Inl x)))"
definition Arrow_T1 :: "('var::var, 'tyvar::var, 'a::var, 'b) T1" where
  "Arrow_T1 \<equiv> T1_ctor (Abs_T1_pre (Inl (Inr (Inl ()))))"
definition TyVar_T1 :: "'tyvar \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T1" where
  "TyVar_T1 a \<equiv> T1_ctor (Abs_T1_pre (Inl (Inr (Inr a))))"
definition App_T1 :: "('var::var, 'tyvar::var, 'a::var, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1" where
  "App_T1 t1 t2 \<equiv> T1_ctor (Abs_T1_pre (Inr (Inl (Inl (t1, t2)))))"
definition Lam_T1 :: "'var \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1" where
  "Lam_T1 x t \<equiv> T1_ctor (Abs_T1_pre (Inr (Inl (Inr (x, t)))))"
definition TyLam_T1 :: "'tyvar \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T1" where
  "TyLam_T1 a t \<equiv> T1_ctor (Abs_T1_pre (Inr (Inr (Inl (a, t)))))"
definition Ext_T1 :: "'a \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T1" where
  "Ext_T1 x \<equiv> T1_ctor (Abs_T1_pre (Inr (Inr (Inr x))))"

definition Var_T2 :: "'var \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T2" where
  "Var_T2 x \<equiv> T2_ctor (Abs_T2_pre (Inl (Inl x)))"
definition TyVar_T2 :: "'tyvar \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T2" where
  "TyVar_T2 a \<equiv> T2_ctor (Abs_T2_pre (Inl (Inr (Inl a))))"
definition App_T2 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T2" where
  "App_T2 t1 t2 \<equiv> T2_ctor (Abs_T2_pre (Inl (Inr (Inr (t1, t2)))))"
definition Lam_T2 :: "'var \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1 list \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T2" where
  "Lam_T2 x t \<equiv> T2_ctor (Abs_T2_pre (Inr (Inl (x, t))))"
definition TyLam_T2 :: "'tyvar \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T2" where
  "TyLam_T2 x t \<equiv> T2_ctor (Abs_T2_pre (Inr (Inr (Inl (x, t)))))"
definition Ext_T2 :: "'b \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::var, 'tyvar::var, 'a::var, 'b) T2" where
  "Ext_T2 b t \<equiv> T2_ctor (Abs_T2_pre (Inr (Inr (Inr (b, t)))))"

lemmas T1_ctors_defs = Var_T1_def Arrow_T1_def TyVar_T1_def App_T1_def Lam_T1_def TyLam_T1_def Ext_T1_def
lemmas T2_ctors_defs = Var_T2_def TyVar_T2_def App_T2_def Lam_T2_def TyLam_T2_def Ext_T2_def

lemmas T1_pre_set_defs = set1_T1_pre_def set2_T1_pre_def set3_T1_pre_def set4_T1_pre_def set5_T1_pre_def set6_T1_pre_def set7_T1_pre_def set8_T1_pre_def set9_T1_pre_def set10_T1_pre_def
lemmas T2_pre_set_defs = set1_T2_pre_def set2_T2_pre_def set3_T2_pre_def set4_T2_pre_def set5_T2_pre_def set6_T2_pre_def set7_T2_pre_def set8_T2_pre_def set9_T2_pre_def set10_T2_pre_def

lemma T1_T2_strong_induct:
  fixes t1::"('var::var, 'tyvar::var, 'a::var, 'b) T1" and t2::"('var::var, 'tyvar::var, 'a::var, 'b) T2"
  assumes
    "\<forall>\<rho>. |K1 \<rho>| <o |UNIV::'var set|"
    "\<forall>\<rho>. |K2 \<rho>| <o |UNIV::'tyvar set|"

    and IHs: "\<And>x \<rho>. P (Var_T1 x) \<rho>"
    "\<And>\<rho>. P Arrow_T1 \<rho>"
    "\<And>a \<rho>. P (TyVar_T1 a) \<rho>"
    "\<And>t1 t2 \<rho>. \<forall>\<rho>. P t1 \<rho> \<Longrightarrow> \<forall>\<rho>. P2 t2 \<rho> \<Longrightarrow> P (App_T1 t1 t2) \<rho>"
    "\<And>x t \<rho>. x \<notin> K1 \<rho> \<Longrightarrow> \<forall>\<rho>. P t \<rho> \<Longrightarrow> P (Lam_T1 x t) \<rho>"
    "\<And>a t \<rho>. a \<notin> K2 \<rho> \<Longrightarrow> \<forall>\<rho>. P t \<rho> \<Longrightarrow> P (TyLam_T1 a t) \<rho>"
    "\<And>a \<rho>. P (Ext_T1 a) \<rho>"

    "\<And>x \<rho>. P2 (Var_T2 x) \<rho>"
    "\<And>a \<rho>. P2 (TyVar_T2 a) \<rho>"
    "\<And>t1 t2 \<rho>. \<forall>\<rho>. P t1 \<rho> \<Longrightarrow> \<forall>\<rho>. P2 t2 \<rho> \<Longrightarrow> P2 (App_T2 t1 t2) \<rho>"
    "\<And>x ts \<rho>. x \<notin> K1 \<rho> \<Longrightarrow> (\<And>t \<rho>. t \<in> set ts \<Longrightarrow> P t \<rho>) \<Longrightarrow> P2 (Lam_T2 x ts) \<rho>"
    "\<And>a t \<rho>. a \<notin> K2 \<rho> \<Longrightarrow> \<forall>\<rho>. P2 t \<rho> \<Longrightarrow> P2 (TyLam_T2 a t) \<rho>"
    "\<And>b t \<rho>. \<forall>\<rho>. P t \<rho> \<Longrightarrow> P2 (Ext_T2 b t) \<rho>"
  shows "\<forall>\<rho>. P t1 \<rho> \<and> P2 t2 \<rho>"
  apply (unfold ball_UNIV[symmetric])
  apply (rule T1.TT_fresh_co_induct_param[of _ K1 K2 P P2 t1 t2])
     apply (rule assms(1,2)[THEN spec])+
  subgoal for v1 \<rho>
    apply (tactic \<open>resolve_tac @{context} [infer_instantiate' @{context} [SOME @{cterm v1}] (
      BNF_FP_Util.mk_absumprodE @{thm type_definition_T1_pre} (map length ctor_T1_Ts)
    )] 1\<close>; hypsubst_thin)
        (* REPEAT_DETERM *)
          apply (subst unit_eq)?
          apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T1_ctors_defs[symmetric] Abs_T1_pre_inverse[OF UNIV_I]
        T1_pre_set_defs
        )[1]
          apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
          apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
          apply (rule IHs(1))
      (* repeated *)
         apply (subst unit_eq)?
         apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T1_ctors_defs[symmetric] Abs_T1_pre_inverse[OF UNIV_I]
        T1_pre_set_defs
        )[1]
         apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
         apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
         apply (rule IHs(2))
      (* repeated *)
        apply (subst unit_eq)?
        apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T1_ctors_defs[symmetric] Abs_T1_pre_inverse[OF UNIV_I]
        T1_pre_set_defs
        )[1]
        apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
        apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
        apply (rule IHs(3))
      (* repeated *)
       apply (subst unit_eq)?
       apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T1_ctors_defs[symmetric] Abs_T1_pre_inverse[OF UNIV_I]
        T1_pre_set_defs
        )[1]
       apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule IHs(4))
      (* REPEAT_DETERM *)
        apply (rule allI)
        apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(1)) (* nonbinding occurence of T1 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I)+
      done
        (* repeated *)
       apply (rule allI)
       apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(3)) (* nonbinding occurence of T2 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I)+
      done
        (* END REPEAT_DETERM *)
        (* repeated *)
      apply (subst unit_eq)?
      apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T1_ctors_defs[symmetric] Abs_T1_pre_inverse[OF UNIV_I]
        T1_pre_set_defs
        )[1]
      apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
      apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
      apply (rule IHs(5))
      (* REPEAT_DETERM *)
       apply (rule allI)?
       apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(5)) (* bound var of type 'var *)
      apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
      apply (rule singletonI UNIV_I UN_I)+
      done
        (* repeated *)
      apply (rule allI)?
      apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(2)) (* binding occurence of T1 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I)+
      done
        (* END REPEAT_DETERM *)
        (* repeated *)
     apply (subst unit_eq)?
     apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T1_ctors_defs[symmetric] Abs_T1_pre_inverse[OF UNIV_I]
        T1_pre_set_defs
        )[1]
     apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
     apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
     apply (rule IHs(6))
      (* REPEAT_DETERM *)
      apply (rule allI)?
      apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(6)) (* bound var of type 'tyvar *)
      apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
      apply (rule singletonI UNIV_I UN_I)+
      done
        (* repeated *)
     apply (rule allI)?
     apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(2)) (* binding occurence of T1 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I)+
      done
        (* END REPEAT_DETERM *)
        (* repeated *)
    apply (subst unit_eq)?
    apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T1_ctors_defs[symmetric] Abs_T1_pre_inverse[OF UNIV_I]
        T1_pre_set_defs
        )[1]
    apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
    apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
    apply (rule IHs(7))
      (* END REPEAT_DETERM *)
    done

  subgoal for v2 \<rho>
    apply (tactic \<open>resolve_tac @{context} [infer_instantiate' @{context} [SOME @{cterm v2}] (
      BNF_FP_Util.mk_absumprodE @{thm type_definition_T2_pre} (map length ctor_T2_Ts)
    )] 1\<close>; hypsubst_thin)
        (* REPEAT_DETERM *)
         apply (subst unit_eq)?
         apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T2_ctors_defs[symmetric] Abs_T2_pre_inverse[OF UNIV_I]
        T2_pre_set_defs
        )[1]
         apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
         apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
         apply (rule IHs(8))
      (* repeated *)
        apply (subst unit_eq)?
        apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T2_ctors_defs[symmetric] Abs_T2_pre_inverse[OF UNIV_I]
        T2_pre_set_defs
        )[1]
        apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
        apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
        apply (rule IHs(9))
      (* repeated *)
       apply (subst unit_eq)?
       apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T2_ctors_defs[symmetric] Abs_T2_pre_inverse[OF UNIV_I]
        T2_pre_set_defs
        )[1]
       apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule IHs(10))
      (* repeated *)
      (* REPEAT_DETERM *)
        apply (rule allI)
        apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(1)) (* nonbinding occurence of T1 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I)+
      done
        (* repeated *)
       apply (rule allI)
       apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(3)) (* nonbinding occurence of T2 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I)+
      done
        (* END REPEAT_DETERM *)
      (* repeated *)
       apply (subst unit_eq)?
       apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T2_ctors_defs[symmetric] Abs_T2_pre_inverse[OF UNIV_I]
        T2_pre_set_defs
        )[1]
       apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
      apply (rule IHs(11))
      (* REPEAT_DETERM *)
        apply (rule allI)?
        apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(5)) (* bound var of type 'var *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I)+
      done
        (* repeated *)
       apply (rule allI)?
       apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(2)) (* binding occurence of T1 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I prems)+
      done
      (* END REPEAT_DETERM *)
      (* repeated *)
       apply (subst unit_eq)?
       apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T2_ctors_defs[symmetric] Abs_T2_pre_inverse[OF UNIV_I]
        T2_pre_set_defs
        )[1]
       apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
      apply (rule IHs(12))
      (* REPEAT_DETERM *)
        apply (rule allI)?
        apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(6)) (* bound var of type 'tyvar *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I)+
      done
        (* repeated *)
       apply (rule allI)?
       apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(4)) (* binding occurence of T2 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I prems)+
      done
      (* END REPEAT_DETERM *)
      (* repeated *)
       apply (subst unit_eq)?
       apply (unfold sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right comp_def
        UN_singleton sum_set_simps prod_set_simps UN_single UN_empty
        T2_ctors_defs[symmetric] Abs_T2_pre_inverse[OF UNIV_I]
        T2_pre_set_defs
        )[1]
       apply (subst (asm) list.set_map, ((rule supp_id_bound bij_id)+)?)? (* For nested BNFs *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
      apply (rule IHs(13))
      (* REPEAT_DETERM *)
       apply (rule allI)?
       apply (rule disjointI)?
    subgoal premises prems
      apply (rule prems(1)) (* nonbinding occurence of T1 *)
       apply (unfold UN_empty UN_empty2 Un_empty_left Un_empty_right)?
       apply (rule singletonI UNIV_I UN_I prems)+
      done
      (* END REPEAT_DETERM *)
    done
  done

lemmas T1_T2_induct = T1_T2_strong_induct[of "\<lambda>_. {}" "\<lambda>_. {}" "\<lambda>t \<rho>. _ t" "\<lambda>t \<rho>. _ t",
  unfolded HOL.simp_thms(35), OF emp_bound emp_bound,
  unfolded notin_empty_eq_True Int_empty_right HOL.simp_thms(6) HOL.True_implies_equals
]

lemmas set_simp_thms = sum.set_map prod.set_map comp_def UN_empty UN_empty2 Un_empty_left Un_empty_right
  UN_singleton UN_single sum_set_simps prod_set_simps Diff_empty UN_Un empty_Diff

lemma set_T1_simps[simp]:
  "FFVars_T11 (Var_T1 x) = {x}"
  "FFVars_T11 Arrow_T1 = {}"
  "FFVars_T11 (TyVar_T1 a) = {}"
  "FFVars_T11 (App_T1 t1 t2) = FFVars_T11 t1 \<union> FFVars_T21 t2"
  "FFVars_T11 (Lam_T1 x t) = FFVars_T11 t - {x}"
  "FFVars_T11 (TyLam_T1 a t) = FFVars_T11 t"
  "FFVars_T11 (Ext_T1 a) = {}"

  "FFVars_T12 (Var_T1 x) = {}"
  "FFVars_T12 Arrow_T1 = {}"
  "FFVars_T12 (TyVar_T1 a) = {a}"
  "FFVars_T12 (App_T1 t1 t2) = FFVars_T12 t1 \<union> FFVars_T22 t2"
  "FFVars_T12 (Lam_T1 x t) = FFVars_T12 t"
  "FFVars_T12 (TyLam_T1 a t) = FFVars_T12 t - {a}"
  "FFVars_T12 (Ext_T1 a) = {}"

  "set3_T1 (Var_T1 x) = {}"
  "set3_T1 Arrow_T1 = {}"
  "set3_T1 (TyVar_T1 a) = {}"
  "set3_T1 (App_T1 t1 t2) = set3_T1 t1 \<union> set3_T2 t2"
  "set3_T1 (Lam_T1 x t) = set3_T1 t"
  "set3_T1 (TyLam_T1 a t) = set3_T1 t"
  "set3_T1 (Ext_T1 a) = {a}"

  "set4_T1 (Var_T1 x) = {}"
  "set4_T1 Arrow_T1 = {}"
  "set4_T1 (TyVar_T1 a) = {}"
  "set4_T1 (App_T1 t1 t2) = set4_T1 t1 \<union> set4_T2 t2"
  "set4_T1 (Lam_T1 x t) = set4_T1 t"
  "set4_T1 (TyLam_T1 a t) = set4_T1 t"
  "set4_T1 (Ext_T1 a) = {}"
  apply (unfold set_simp_thms T1_ctors_defs T1.FFVars_cctors
      T1_pre_set_defs Abs_T1_pre_inverse[OF UNIV_I]
      T1_set_simps
  )
                      apply (rule refl)+
  done

lemma set_T2_simps[simp]:
  "FFVars_T21 (Var_T2 x) = {x}"
  "FFVars_T21 (TyVar_T2 a) = {}"
  "FFVars_T21 (App_T2 t1 t2) = FFVars_T11 t1 \<union> FFVars_T21 t2"
  "FFVars_T21 (Lam_T2 x ts) = \<Union>(FFVars_T11 ` set ts)- {x}"
  "FFVars_T21 (TyLam_T2 a t) = FFVars_T21 t"
  "FFVars_T21 (Ext_T2 b t1) = FFVars_T11 t1"

  "FFVars_T22 (Var_T2 x) = {}"
  "FFVars_T22 (TyVar_T2 a) = {a}"
  "FFVars_T22 (App_T2 t1 t2) = FFVars_T12 t1 \<union> FFVars_T22 t2"
  "FFVars_T22 (Lam_T2 x ts) = \<Union>(FFVars_T12 ` set ts)"
  "FFVars_T22 (TyLam_T2 a t) = FFVars_T22 t"
  "FFVars_T22 (Ext_T2 b t1) = FFVars_T12 t1"

  "set3_T2 (Var_T2 x) = {}"
  "set3_T2 (TyVar_T2 a) = {}"
  "set3_T2 (App_T2 t1 t2) = set3_T1 t1 \<union> set3_T2 t2"
  "set3_T2 (Lam_T2 x ts) = \<Union>(set3_T1 ` set ts)"
  "set3_T2 (TyLam_T2 a t) = set3_T2 t"
  "set3_T2 (Ext_T2 b t1) = set3_T1 t1"

  "set4_T2 (Var_T2 x) = {}"
  "set4_T2 (TyVar_T2 a) = {}"
  "set4_T2 (App_T2 t1 t2) = set4_T1 t1 \<union> set4_T2 t2"
  "set4_T2 (Lam_T2 x ts) = \<Union>(set4_T1 ` set ts)"
  "set4_T2 (TyLam_T2 a t) = set4_T2 t"
  "set4_T2 (Ext_T2 b t1) = {b} \<union> set4_T1 t1"
apply (unfold set_simp_thms T2_ctors_defs T1.FFVars_cctors
      T2_pre_set_defs Abs_T2_pre_inverse[OF UNIV_I]
      T2_set_simps
  )
                      apply (rule refl)+
  done

lemma T1_distinct[simp]:
  "Var_T1 x \<noteq> Arrow_T1"
  "Var_T1 x \<noteq> TyVar_T1 a"
  "Var_T1 x \<noteq> App_T1 t1 t2"
  "Var_T1 x \<noteq> Lam_T1 a1 t"
  "Var_T1 x \<noteq> TyLam_T1 a2 t1"
  "Var_T1 x \<noteq> Ext_T1 a3"

  "Arrow_T1 \<noteq> Var_T1 x"
  "Arrow_T1 \<noteq> TyVar_T1 a"
  "Arrow_T1 \<noteq> App_T1 t1 t2"
  "Arrow_T1 \<noteq> Lam_T1 a1 t"
  "Arrow_T1 \<noteq> TyLam_T1 a2 t1"
  "Arrow_T1 \<noteq> Ext_T1 a3"

  "TyVar_T1 a \<noteq> Var_T1 x"
  "TyVar_T1 a \<noteq> Arrow_T1"
  "TyVar_T1 a \<noteq> App_T1 t1 t2"
  "TyVar_T1 a \<noteq> Lam_T1 a1 t"
  "TyVar_T1 a \<noteq> TyLam_T1 a2 t1"
  "TyVar_T1 a \<noteq> Ext_T1 a3"

  "App_T1 t1 t2 \<noteq> Var_T1 x"
  "App_T1 t1 t2 \<noteq> Arrow_T1"
  "App_T1 t1 t2 \<noteq> TyVar_T1 a"
  "App_T1 t1 t2 \<noteq> Lam_T1 a1 t"
  "App_T1 t1 t2 \<noteq> TyLam_T1 a2 t1"
  "App_T1 t1 t2 \<noteq> Ext_T1 a3"

  "Lam_T1 a1 t \<noteq> Var_T1 x"
  "Lam_T1 a1 t \<noteq> Arrow_T1"
  "Lam_T1 a1 t \<noteq> TyVar_T1 a"
  "Lam_T1 a1 t \<noteq> App_T1 t1 t2"
  "Lam_T1 a1 t \<noteq> TyLam_T1 a2 t1"
  "Lam_T1 a1 t \<noteq> Ext_T1 a3"

  "TyLam_T1 a2 t1 \<noteq> Var_T1 x"
  "TyLam_T1 a2 t1 \<noteq> Arrow_T1"
  "TyLam_T1 a2 t1 \<noteq> TyVar_T1 a"
  "TyLam_T1 a2 t1 \<noteq> App_T1 t1 t2"
  "TyLam_T1 a2 t1 \<noteq> Lam_T1 a1 t"
  "TyLam_T1 a2 t1 \<noteq> Ext_T1 a3"

  "Ext_T1 a3 \<noteq> Var_T1 x"
  "Ext_T1 a3 \<noteq> Arrow_T1"
  "Ext_T1 a3 \<noteq> TyVar_T1 a"
  "Ext_T1 a3 \<noteq> App_T1 t1 t2"
  "Ext_T1 a3 \<noteq> Lam_T1 a1 t"
  "Ext_T1 a3 \<noteq> TyLam_T1 a2 t1"
                      apply (unfold comp_def map_sum.simps map_prod_simp sum.inject
    T1_ctors_defs T1.TT_injects0 map_T1_pre_def
    Abs_T1_pre_inverse[OF UNIV_I] Abs_T1_pre_inject[OF UNIV_I UNIV_I]
)
                      apply (rule notI, (erule exE conjE sum.distinct[THEN notE])+)+
  done

lemma T2_distinct[simp]:
  "Var_T2 x \<noteq> TyVar_T2 a"
  "Var_T2 x \<noteq> App_T2 t1 t2"
  "Var_T2 x \<noteq> Lam_T2 x1 t3"
  "Var_T2 x \<noteq> TyLam_T2 a2 t4"
  "Var_T2 x \<noteq> Ext_T2 a3 t5"

  "TyVar_T2 a \<noteq> Var_T2 x"
  "TyVar_T2 a \<noteq> App_T2 t1 t2"
  "TyVar_T2 a \<noteq> Lam_T2 x1 t3"
  "TyVar_T2 a \<noteq> TyLam_T2 a2 t4"
  "TyVar_T2 a \<noteq> Ext_T2 a3 t5"

  "App_T2 t1 t2 \<noteq> Var_T2 x"
  "App_T2 t1 t2 \<noteq> TyVar_T2 a"
  "App_T2 t1 t2 \<noteq> Lam_T2 x1 t3"
  "App_T2 t1 t2 \<noteq> TyLam_T2 a2 t4"
  "App_T2 t1 t2 \<noteq> Ext_T2 a3 t5"

  "Lam_T2 x1 t3 \<noteq> Var_T2 x"
  "Lam_T2 x1 t3 \<noteq> TyVar_T2 a"
  "Lam_T2 x1 t3 \<noteq> App_T2 t1 t2"
  "Lam_T2 x1 t3 \<noteq> TyLam_T2 a2 t4"
  "Lam_T2 x1 t3 \<noteq> Ext_T2 a3 t5"

  "TyLam_T2 a2 t4 \<noteq> Var_T2 x"
  "TyLam_T2 a2 t4 \<noteq> TyVar_T2 a"
  "TyLam_T2 a2 t4 \<noteq> App_T2 t1 t2"
  "TyLam_T2 a2 t4 \<noteq> Lam_T2 x1 t3"
  "TyLam_T2 a2 t4 \<noteq> Ext_T2 a3 t5"

  "Ext_T2 a3 t5 \<noteq> Var_T2 x"
  "Ext_T2 a3 t5 \<noteq> TyVar_T2 a"
  "Ext_T2 a3 t5 \<noteq> App_T2 t1 t2"
  "Ext_T2 a3 t5 \<noteq> Lam_T2 x1 t3"
  "Ext_T2 a3 t5 \<noteq> TyLam_T2 a2 t4"
                      apply (unfold comp_def map_sum.simps map_prod_simp sum.inject
    T2_ctors_defs T1.TT_injects0 map_T2_pre_def
    Abs_T2_pre_inverse[OF UNIV_I] Abs_T2_pre_inject[OF UNIV_I UNIV_I]
)
                      apply (rule notI, (erule exE conjE sum.distinct[THEN notE])+)+
  done

abbreviation eta11 :: "'a \<Rightarrow> ('a::var, 'b::var, 'c::var, 'd, 'e::var, 'f::var, 'g, 'h, 'i, 'j) T1_pre" where
  "eta11 x \<equiv> Abs_T1_pre (Inl (Inl x))"
abbreviation eta12 :: "'b \<Rightarrow> ('a::var, 'b::var, 'c::var, 'd, 'e::var, 'f::var, 'g, 'h, 'i, 'j) T1_pre" where
  "eta12 x \<equiv> Abs_T1_pre (Inl (Inr (Inr x)))"
abbreviation eta21 :: "'a \<Rightarrow> ('a::var, 'b::var, 'c::var, 'd, 'e::var, 'f::var, 'g, 'h, 'i, 'j) T2_pre" where
  "eta21 x \<equiv> Abs_T2_pre (Inl (Inl x))"

lemma eta_frees:
  "set1_T1_pre (eta11 x) = {x}"
  "set2_T1_pre (eta12 x2) = {x2}"
  "set1_T2_pre (eta21 x3) = {x3}"
    apply (unfold set_simp_thms T1_pre_set_defs Abs_T1_pre_inverse[OF UNIV_I]
      T2_pre_set_defs Abs_T2_pre_inverse[OF UNIV_I])
    apply (rule refl)+
  done

lemma eta_injs:
  "eta11 a = eta11 a' \<Longrightarrow> a = a'"
  "eta12 a2 = eta12 a2' \<Longrightarrow> a2 = a2'"
  "eta21 a3 = eta21 a3' \<Longrightarrow> a3 = a3'"
    apply (unfold sum.inject Abs_T1_pre_inject[OF UNIV_I UNIV_I] Abs_T2_pre_inject[OF UNIV_I UNIV_I])
    apply assumption+
  done

lemma eta_compl_frees:
  "x \<notin> range eta11 \<Longrightarrow> set1_T1_pre x = {}"
  "x2 \<notin> range eta12 \<Longrightarrow> set2_T1_pre x2 = {}"
  "x3 \<notin> range eta21 \<Longrightarrow> set1_T2_pre x3 = {}"
  subgoal
    apply (unfold set_simp_thms T1_pre_set_defs)
    apply (rule Abs_T1_pre_cases[of x])
    apply hypsubst_thin
    apply (unfold image_iff bex_UNIV Abs_T1_pre_inverse[OF UNIV_I] Abs_T1_pre_inject[OF UNIV_I UNIV_I])
    apply (erule contrapos_np)
    apply (drule iffD2[OF ex_in_conv])
    apply (erule exE)
    apply (erule UN_E)+
    apply (erule setl.cases setr.cases)+
    apply hypsubst
    apply (rule exI)
    apply (rule refl)
    done
  subgoal
    apply (unfold set_simp_thms T1_pre_set_defs)
    apply (rule Abs_T1_pre_cases[of x2])
    apply hypsubst_thin
    apply (unfold image_iff bex_UNIV Abs_T1_pre_inverse[OF UNIV_I] Abs_T1_pre_inject[OF UNIV_I UNIV_I])
    apply (erule contrapos_np)
    apply (drule iffD2[OF ex_in_conv])
    apply (erule exE)
    apply (erule UN_E)+
    apply (erule setl.cases setr.cases)+
    apply hypsubst
    apply (rule exI)
    apply (rule refl)
    done
  subgoal
    apply (unfold set_simp_thms T2_pre_set_defs)
    apply (rule Abs_T2_pre_cases[of x3])
    apply hypsubst_thin
    apply (unfold image_iff bex_UNIV Abs_T2_pre_inverse[OF UNIV_I] Abs_T2_pre_inject[OF UNIV_I UNIV_I])
    apply (erule contrapos_np)
    apply (drule iffD2[OF ex_in_conv])
    apply (erule exE)
    apply (erule UN_E)+
    apply (erule setl.cases setr.cases)+
    apply hypsubst
    apply (rule exI)
    apply (rule refl)
    done
  done

lemma eta_naturals:
  fixes f1::"('x1::var \<Rightarrow> 'x1)" and f2::"('x2::var \<Rightarrow> 'x2)"
    and f3::"('x3::var \<Rightarrow> 'x3)" and f4::"('x4::var \<Rightarrow> 'x4)"
  assumes "|supp f1| <o |UNIV::'x1 set|" "|supp f2| <o |UNIV::'x2 set|"
      and "bij f3" "|supp f3| <o |UNIV::'x3 set|" "bij f4" "|supp f4| <o |UNIV::'x4 set|"
    shows
      "map_T1_pre f1 f2 id id f3 f4 f5 f6 f7 f8 \<circ> eta11 = eta11 \<circ> f1"
      "map_T1_pre f1 f2 id id f3 f4 f5 f6 f7 f8 \<circ> eta12 = eta12 \<circ> f2"
      "map_T2_pre f1 f2 id id f3 f4 f5 f6 f7 f8 \<circ> eta21 = eta21 \<circ> f1"
    apply (unfold comp_def map_sum.simps Abs_T1_pre_inverse[OF UNIV_I]
      map_T1_pre_def map_T2_pre_def Abs_T2_pre_inverse[OF UNIV_I]
    )
    apply (rule refl)+
  done

ML \<open>
val T1_model = {
  binding = @{binding tvsubst_T1},
  etas = [
    SOME (@{term "eta11"}, {
      eta_free = fn ctxt => resolve_tac ctxt @{thms eta_frees} 1,
      eta_inj = fn ctxt => eresolve_tac ctxt @{thms eta_injs} 1,
      eta_compl_free = fn ctxt => eresolve_tac ctxt @{thms eta_compl_frees} 1,
      eta_natural = fn ctxt => HEADGOAL (resolve_tac ctxt @{thms eta_naturals} THEN_ALL_NEW assume_tac ctxt)
    }),
    SOME (@{term "eta12"}, {
      eta_free = fn ctxt => resolve_tac ctxt @{thms eta_frees} 1,
      eta_inj = fn ctxt => eresolve_tac ctxt @{thms eta_injs} 1,
      eta_compl_free = fn ctxt => eresolve_tac ctxt @{thms eta_compl_frees} 1,
      eta_natural = fn ctxt => HEADGOAL (resolve_tac ctxt @{thms eta_naturals} THEN_ALL_NEW assume_tac ctxt)
    })
  ]
};
val T2_model = {
  binding = @{binding tvsubst_T2},
  etas = [
    SOME (@{term "eta21"}, {
      eta_free = fn ctxt => resolve_tac ctxt @{thms eta_frees} 1,
      eta_inj = fn ctxt => eresolve_tac ctxt @{thms eta_injs} 1,
      eta_compl_free = fn ctxt => eresolve_tac ctxt @{thms eta_compl_frees} 1,
      eta_natural = fn ctxt => HEADGOAL (resolve_tac ctxt @{thms eta_naturals} THEN_ALL_NEW assume_tac ctxt)
    }),
    NONE
  ]
};
\<close>

ML_file \<open>../Tools/mrbnf_tvsubst.ML\<close>

local_setup \<open>fn lthy =>
let
  val (res', lthy) = MRBNF_TVSubst.create_tvsubst_of_mrbnf I res [T1_model, T2_model] lthy
  val _ = @{print} res'
in lthy end\<close>
print_theorems

end