theory BMV_Monad
  imports "Binders.MRBNF_Recursor"
begin

declare [[mrbnf_internals]]
binder_datatype 'a FType
  = TyVar 'a
  | TyApp "'a FType" "'a FType"
  | TyAll a::'a t::"'a FType" binds a in t

(*
SOps = { 'a FType }
L = 'a FType
m = 1
*)
abbreviation Inj_FType_1 :: "'tyvar::var \<Rightarrow> 'tyvar FType" where "Inj_FType_1 \<equiv> TyVar"
abbreviation Sb_FType :: "('tyvar::var \<Rightarrow> 'tyvar FType) \<Rightarrow> 'tyvar FType \<Rightarrow> 'tyvar FType" where "Sb_FType \<equiv> tvsubst_FType"
abbreviation Vrs_FType_1 :: "'tyvar::var FType \<Rightarrow> 'tyvar set" where "Vrs_FType_1 \<equiv> FVars_FType"

lemma VVr_eq_Var: "tvVVr_tvsubst_FType = TyVar"
  unfolding tvVVr_tvsubst_FType_def TyVar_def comp_def tv\<eta>_FType_tvsubst_FType_def by (rule refl)

lemma SSupp_Inj_FType[simp]: "SSupp_FType Inj_FType_1 = {}" unfolding SSupp_FType_def tvVVr_tvsubst_FType_def TyVar_def tv\<eta>_FType_tvsubst_FType_def by simp
lemma IImsupp_Inj_FType[simp]: "IImsupp_FType Inj_FType_1 = {}" unfolding IImsupp_FType_def by simp
lemma SSupp_IImsupp_bound[simp]:
  fixes \<rho>::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "|IImsupp_FType \<rho>| <o |UNIV::'tyvar set|"
  unfolding IImsupp_FType_def using assms by (auto simp: FType.Un_bound FType.UN_bound FType.set_bd_UNIV)

lemma SSupp_comp_subset:
  fixes \<rho> \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "SSupp_FType (tvsubst_FType \<rho> \<circ> \<rho>') \<subseteq> SSupp_FType \<rho> \<union> SSupp_FType \<rho>'"
  unfolding SSupp_FType_def tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def comp_def
  apply (unfold TyVar_def[symmetric])
  apply (rule subsetI)
  apply (unfold mem_Collect_eq)
  apply simp
  using assms(1) by force
lemma SSupp_comp_bound[simp]:
  fixes \<rho> \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  shows "|SSupp_FType (tvsubst_FType \<rho> \<circ> \<rho>')| <o |UNIV::'tyvar set|"
  using assms SSupp_comp_subset by (metis card_of_subset_bound var_class.Un_bound)

lemma Sb_Inj_FType: "Sb_FType Inj_FType_1 = id"
  apply (rule ext)
  subgoal for x
    apply (induction x)
    by auto
  done
lemma Sb_comp_Inj_FType:
  fixes \<rho>::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>| <o |UNIV::'tyvar set|"
  shows "Sb_FType \<rho> \<circ> Inj_FType_1 = \<rho>"
  using assms by auto

lemma Sb_comp_FType:
  fixes \<rho>'' \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>''| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  shows "Sb_FType \<rho>'' \<circ> Sb_FType \<rho>' = Sb_FType (Sb_FType \<rho>'' \<circ> \<rho>')"
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  subgoal for x
    apply (binder_induction x avoiding: "IImsupp_FType \<rho>''" "IImsupp_FType \<rho>'" "IImsupp_FType (Sb_FType \<rho>'' \<circ> \<rho>')" rule: FType.strong_induct)
    using assms by (auto simp: IImsupp_FType_def FType.Un_bound FType.UN_bound FType.set_bd_UNIV)
  done
thm Sb_comp_FType[unfolded SSupp_FType_def tvVVr_tvsubst_FType_def[unfolded comp_def] tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric]]
lemma Vrs_Inj_FType: "Vrs_FType_1 (Inj_FType_1 a) = {a}"
  by simp

lemma Vrs_Sb_FType:
  fixes \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  shows "Vrs_FType_1 (Sb_FType \<rho>' x) = (\<Union>a\<in>Vrs_FType_1 x. Vrs_FType_1 (\<rho>' a))"
proof (binder_induction x avoiding: "IImsupp_FType \<rho>'" rule: FType.strong_induct)
  case (TyAll x1 x2)
  then show ?case using assms by (auto intro!: FType.IImsupp_Diff[symmetric])
qed (auto simp: assms)

lemma Sb_cong_FType:
  fixes \<rho>'' \<rho>'::"'tyvar::var \<Rightarrow> 'tyvar FType"
  assumes "|SSupp_FType \<rho>''| <o |UNIV::'tyvar set|" "|SSupp_FType \<rho>'| <o |UNIV::'tyvar set|"
  and "\<And>a. a \<in> Vrs_FType_1 t \<Longrightarrow> \<rho>'' a = \<rho>' a"
  shows "Sb_FType \<rho>'' t = Sb_FType \<rho>' t"
using assms(3) proof (binder_induction t avoiding: "IImsupp_FType \<rho>''" "IImsupp_FType \<rho>'" rule: FType.strong_induct)
  case (TyAll x1 x2)
  then show ?case using assms apply auto
    by (smt (verit, ccfv_threshold) CollectI IImsupp_FType_def SSupp_FType_def Un_iff)
qed (auto simp: assms(1-2))

ML_file \<open>../Tools/bmv_monad_def.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 0
\<close>

ML \<open>
val model_FType = {
  ops = [@{typ "'a::var FType"}],
  bd = @{term natLeq},
  var_class = @{class var},
  leader = 0,
  frees = [@{typ "'a::var"}],
  lives = [],
  bmv_ops = [],
  Injs = [[@{term "TyVar :: 'a::var \<Rightarrow> _"}]],
  Sbs = [@{term "tvsubst_FType :: _ => 'a::var FType => _"}],
  Maps = [NONE],
  Vrs = [[[SOME @{term "FVars_FType :: _ => 'a::var set"}]]],
  tacs = [{
    Sb_Inj = fn ctxt => resolve_tac ctxt @{thms Sb_Inj_FType} 1,
    Sb_comp_Injs = [fn ctxt => EVERY1 [
      resolve_tac ctxt @{thms Sb_comp_Inj_FType},
      K (Local_Defs.unfold0_tac ctxt @{thms SSupp_FType_def VVr_eq_Var}),
      assume_tac ctxt
    ]],
    Sb_comp = fn ctxt => EVERY1 [
      resolve_tac ctxt @{thms Sb_comp_FType},
      K (Local_Defs.unfold0_tac ctxt @{thms SSupp_FType_def VVr_eq_Var}),
      REPEAT_DETERM o assume_tac ctxt
    ],
    Vrs_Injs = [[SOME (fn ctxt => resolve_tac ctxt @{thms Vrs_Inj_FType} 1)]],
    Vrs_Sbs = [[SOME (fn ctxt => EVERY1 [
      resolve_tac ctxt @{thms Vrs_Sb_FType},
      K (Local_Defs.unfold0_tac ctxt @{thms SSupp_FType_def VVr_eq_Var}),
      assume_tac ctxt
    ])]],
    Sb_cong = fn ctxt => EVERY1 [
      resolve_tac ctxt @{thms Sb_cong_FType},
      K (Local_Defs.unfold0_tac ctxt @{thms SSupp_FType_def VVr_eq_Var}),
      REPEAT_DETERM o assume_tac ctxt,
      Goal.assume_rule_tac ctxt
    ]
  } : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_axioms]
} : BMV_Monad_Def.bmv_monad_model;
\<close>

ML \<open>
val FType_bmv = fst (BMV_Monad_Def.bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) I model_FType @{context})
\<close>


(* *)
type_synonym ('a1, 'a2, 'c1, 'c2) L = "'a1 * 'a1 * ('c1 + 'c2)" (* PBMV *)
        type_synonym ('a1, 'a2, 'c1, 'c2) L_M1 = "'a1" (* PBMV *)

type_synonym ('a1, 'a2) L1 = "'a1 * 'a2"
        type_synonym ('a1, 'a2) L1_M1 = "'a1"
        type_synonym ('a1, 'a2) L1_M2 = "'a2"

type_synonym ('a1, 'a2) L2 = "'a1 * 'a2 * 'a2 * 'a2 FType"
        type_synonym ('a1, 'a2) L2_M1 = "'a1"
        type_synonym ('a1, 'a2) L2_M2 = "'a2"
        type_synonym ('a1, 'a2) L2_M3 = "'a2 FType"

(* Dispatcher *)
                  (* from L_M1 *)
definition Sb_L :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L" where
  "Sb_L \<equiv> \<lambda>f. map_prod f (map_prod f id)"
definition Vrs_L_1 :: "('a1, 'a2, 'c1, 'c2) L \<Rightarrow> 'a1 set" where
  "Vrs_L_1 \<equiv> \<lambda>(a1, a1', p). {a1, a1'}" (* corresponds to L_M1 and Inj_L_M1_1 *)
definition Vrs_L_2 :: "('a1, 'a2, 'c1, 'c2) L \<Rightarrow> 'a2 set" where
  "Vrs_L_2 \<equiv> \<lambda>x. {}" (* corresponds to nothing *)
definition Map_L :: "('c1 \<Rightarrow> 'c1') \<Rightarrow> ('c2 \<Rightarrow> 'c2') \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L \<Rightarrow> ('a1, 'a2, 'c1', 'c2') L" where
  "Map_L \<equiv> \<lambda>f1 f2 (a1, a2, p). (a1, a2, map_sum f1 f2 p)"

(* and its minion *)
definition Inj_L_M1_1 :: "'a1 \<Rightarrow> 'a1" where "Inj_L_M1_1 \<equiv> id"
definition Sb_L_M1 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L_M1 \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L_M1" where
  "Sb_L_M1 \<equiv> \<lambda>f. f"
definition Vrs_L_M1_1 :: "'a1 \<Rightarrow> 'a1 set" where "Vrs_L_M1_1 \<equiv> \<lambda>x. {x}"
definition Vrs_L_M1_2 :: "'a2 \<Rightarrow> 'a2 set" where "Vrs_L_M1_2 \<equiv> \<lambda>x. {}"
definition Map_L_M1 :: "('c1 \<Rightarrow> 'c1') \<Rightarrow> ('c2 \<Rightarrow> 'c2') \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L_M1 \<Rightarrow> ('a1, 'a2, 'c1', 'c2') L_M1" where
  "Map_L_M1 \<equiv> \<lambda>f1 f2 x. x"

(* L1 *)
definition Sb_L1 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a2 \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2) L1 \<Rightarrow> ('a1, 'a2) L1" where
  "Sb_L1 \<equiv> \<lambda>f1 f2. map_prod f1 f2"
definition Vrs_L1_1 :: "('a1, 'a2) L1 \<Rightarrow> 'a1 set" where
  "Vrs_L1_1 \<equiv> \<lambda>(a1, a2). {a1}" (* corresponds to L1_M1 and Inj_L1_M1_1 *)
definition Vrs_L1_2 :: "('a1, 'a2) L1 \<Rightarrow> 'a2 set" where
  "Vrs_L1_2 \<equiv> \<lambda>(a1, a2). {a2}" (* corresponds to L1_M2 and Inj_L1_M2_2 *)
(* and its minions M1 *)
definition Sb_L1_M1 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a1, 'a2) L1_M1 \<Rightarrow> ('a1, 'a2) L1_M1" where
  "Sb_L1_M1 \<equiv> \<lambda>f. f"
definition Vrs_L1_M1_1 :: "('a1, 'a2) L1_M1 \<Rightarrow> 'a1 set" where
  "Vrs_L1_M1_1 \<equiv> \<lambda>a. {a}" (* corresponds to L1_M1 and Inj_L1_M1_1 *)
definition Vrs_L1_M1_2 :: "('a1, 'a2) L1_M1 \<Rightarrow> 'a2 set" where
  "Vrs_L1_M1_2 \<equiv> \<lambda>a. {}" (* corresponds to L1_M2 and Inj_L1_M2_2 *)
(* and its minions M2 *)
definition Sb_L1_M2 :: "('a2 \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2) L1_M2 \<Rightarrow> ('a1, 'a2) L1_M2" where
  "Sb_L1_M2 \<equiv> \<lambda>f. f"
definition Vrs_L1_M2_1 :: "('a1, 'a2) L1_M2 \<Rightarrow> 'a1 set" where
  "Vrs_L1_M2_1 \<equiv> \<lambda>a. {}" (* corresponds to L1_M1 and Inj_L1_M1_1 *)
definition Vrs_L1_M2_2 :: "('a1, 'a2) L1_M2 \<Rightarrow> 'a2 set" where
  "Vrs_L1_M2_2 \<equiv> \<lambda>a. {a}" (* corresponds to L1_M2 and Inj_L1_M2_2 *)

(* L2 *)
(* its minions M1, shared with L1_M1 *)
(*definition Sb_L2_M1 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a1, 'a2) L2_M1 \<Rightarrow> ('a1, 'a2) L2_M1" where
  "Sb_L2_M1 \<equiv> \<lambda>f. f"
definition Vrs_L2_M1_1 :: "('a1, 'a2) L2_M1 \<Rightarrow> 'a1 set" where
  "Vrs_L2_M1_1 \<equiv> \<lambda>a. {a}" (* corresponds to L2_M1 and Inj_L2_M1_1 *)
definition Vrs_L2_M1_2 :: "('a1, 'a2) L2_M1 \<Rightarrow> 'a2 set" where
  "Vrs_L2_M1_2 \<equiv> \<lambda>a. {}" (* corresponds to L2_M2 and Inj_L2_M2_2 *) *)
(* and its minions M2 *)
definition Sb_L2_M2 :: "('a2::var \<Rightarrow> 'a2 FType) \<Rightarrow> ('a1, 'a2) L2_M3 \<Rightarrow> ('a1, 'a2) L2_M3" where
  "Sb_L2_M2 \<equiv> tvsubst_FType"
definition Vrs_L2_M2_1 :: "('a1, 'a2) L2_M2 \<Rightarrow> 'a1 set" where
  "Vrs_L2_M2_1 \<equiv> \<lambda>a. {}" (* corresponds to L2_M1 and Inj_L2_M1_1 *)
definition Vrs_L2_M2_2 :: "('a1, 'a2::var) L2_M3 \<Rightarrow> 'a2 set" where
  "Vrs_L2_M2_2 \<equiv> FVars_FType" (* corresponds to L2_M2 and Inj_L2_M2_2 *)
(* and then the leader L2 itself *)
definition Sb_L2 :: "('a1 \<Rightarrow> 'a1) \<Rightarrow> ('a2 \<Rightarrow> 'a2) \<Rightarrow> ('a2::var \<Rightarrow> 'a2 FType) \<Rightarrow> ('a1, 'a2) L2 \<Rightarrow> ('a1, 'a2) L2" where
  "Sb_L2 \<equiv> \<lambda>f1 f2 f3. map_prod (id f1) (map_prod (id f2) (map_prod (id f2) (tvsubst_FType f3)))"
definition Vrs_L2_1 :: "('a1, 'a2) L2 \<Rightarrow> 'a1 set" where
  "Vrs_L2_1 \<equiv> \<lambda>(x,x2,x3,x4). {x}" (* corresponds to L2_M1 and Inj_L2_M1_1 *)
definition Vrs_L2_2 :: "('a1, 'a2::var) L2 \<Rightarrow> 'a2 set" where
  "Vrs_L2_2 \<equiv> \<lambda>(x,x2,x3,x4). {x2,x3}" (* corresponds to L2_M2 and Inj_L2_M2_2 *)
definition Vrs_L2_3 :: "('a1, 'a2::var) L2 \<Rightarrow> 'a2 set" where
  "Vrs_L2_3 \<equiv> \<lambda>(x,x2,x3,x4). FVars_FType x4" (* corresponds to L2_M2 and Inj_L2_M2_2 *)

(* Composition *)
type_synonym ('a1, 'a2) LC = "('a1, 'a2, ('a1, 'a2) L1, ('a1, 'a2) L2) L"
typ "('a1, 'a2, 'c1, 'c2) L"
typ "('a1, 'a2) L1"
typ "('a1, 'a2) LC"
type_synonym ('a1, 'a2) L_MC = "('a1, 'a2, ('a1, 'a2) L1, ('a1, 'a2) L2) L_M1"
typ "('a1, 'a2) L_MC" (* is the same as LC_M1, so do not add *)

typ "('a1, 'a2) L1_M1"
typ "('a1, 'a2) L1_M2"
typ "('a1, 'a2) L2_M2"

declare [[ML_print_depth=10000]]

ML \<open>
val model_ID = {
  ops = [@{typ "'a"}],
  bd = @{term natLeq},
  var_class = @{class var},
  leader = 0,
  frees = [@{typ "'a"}],
  lives = [],
  bmv_ops = [],
  Maps = [NONE],
  Injs = [[@{term "id :: 'a \<Rightarrow> _"}]],
  Sbs = [@{term "id :: _ => 'a => 'a"}],
  Vrs = [[[SOME @{term "\<lambda>(x::'a). {x}"}]]],
  tacs = [{
    Sb_Inj = fn ctxt => resolve_tac ctxt @{thms id_apply} 1,
    Sb_comp_Injs = [fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms comp_def id_def}),
      resolve_tac ctxt [refl]
    ]],
    Sb_comp = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms comp_def id_def}),
      resolve_tac ctxt [refl]
    ],
    Vrs_Injs = [[SOME (fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms comp_def id_def}),
      resolve_tac ctxt [refl]
    ])]],
    Vrs_Sbs = [[SOME (fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms UN_single id_def}),
      resolve_tac ctxt [refl]
    ])]],
    Sb_cong = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms comp_def id_def}),
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms singletonI},
      assume_tac ctxt
    ]
  } : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_axioms]
} : BMV_Monad_Def.bmv_monad_model;
\<close>
ML \<open>
val id_bmv = fst (BMV_Monad_Def.bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) I model_ID @{context})
\<close>

ML \<open>
val model_L = {
  ops = [@{typ "'a1 * 'a1 * ('c1 + 'c2)"}],
  bd = @{term natLeq},
  var_class = @{class var},
  leader = 0,
  frees = [@{typ "'a1"}],
  lives = [@{typ "'c1"}, @{typ "'c2"}],
  bmv_ops = [BMV_Monad_Def.morph_bmv_monad (
    MRBNF_Util.subst_typ_morphism (
      BMV_Monad_Def.frees_of_bmv_monad id_bmv ~~ [@{typ "'a1"}]
  )) id_bmv],
  Maps = [SOME @{term "\<lambda>(f1::'c1 => 'c1') (f2::'c2 => 'c2') (a1::'a1, a2::'a1, p). (a1, a2, map_sum f1 f2 p)"}],
  Injs = [[@{term "id :: 'a1 \<Rightarrow> 'a1"}]],
  Sbs = [@{term "Sb_L :: _ \<Rightarrow> _ \<Rightarrow> ('a1, 'a2, 'c1, 'c2) L"}],
  Vrs = [[[
    SOME @{term "\<lambda>(x1::'a1, x2::'a1, p::'c1 + 'c2). {x1, x2}"}
  ]]],
  tacs = [{
    Sb_Inj = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L_def prod.map_id0}),
      resolve_tac ctxt [refl]
    ],
    Sb_comp_Injs = [],
    Sb_comp = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        (BNF_Def.map_comp0_of_bnf (the (BNF_Def.bnf_of @{context} "Product_Type.prod")) RS sym)
        :: @{thms Sb_L_def id_o id_apply}
      )),
      resolve_tac ctxt [refl]
    ],
    Vrs_Injs = [],
    Vrs_Sbs = [[SOME (fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L_def case_prod_beta
        Product_Type.fst_map_prod Product_Type.snd_map_prod
        UN_insert UN_empty Un_empty_right insert_is_Un[symmetric]
      }),
      resolve_tac ctxt [refl]
    ])]],
    Sb_cong = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L_def case_prod_beta}),
      resolve_tac ctxt @{thms prod.map_cong0},
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms insertI1},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      hyp_subst_tac ctxt,
      assume_tac ctxt,
      resolve_tac ctxt @{thms prod.map_cong0},
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms insertI2},
      resolve_tac ctxt @{thms singletonI},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      hyp_subst_tac ctxt,
      assume_tac ctxt,
      resolve_tac ctxt [refl]
    ]
  } : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_axioms]
} : BMV_Monad_Def.bmv_monad_model;
\<close>
ML \<open>
val L_bmv = fst (BMV_Monad_Def.bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) I model_L @{context})
\<close>

ML \<open>
val model_L1 = {
  ops = [@{typ "'a1 * 'a2"}],
  bd = @{term natLeq},
  var_class = @{class var},
  leader = 0,
  frees = [@{typ "'a1"}, @{typ "'a2"}],
  lives = [],
  bmv_ops = [
    BMV_Monad_Def.morph_bmv_monad (
      MRBNF_Util.subst_typ_morphism (
        BMV_Monad_Def.frees_of_bmv_monad id_bmv ~~ [@{typ "'a1"}]
    )) id_bmv,
    BMV_Monad_Def.morph_bmv_monad (
      MRBNF_Util.subst_typ_morphism (
        BMV_Monad_Def.frees_of_bmv_monad id_bmv ~~ [@{typ "'a2"}]
    )) id_bmv
  ],
  Maps = [NONE],
  Injs = [[@{term "id :: 'a1 \<Rightarrow> 'a1"}, @{term "id :: 'a2 \<Rightarrow> 'a2"}]],
  Sbs = [@{term "Sb_L1 :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a1, 'a2) L1"}],
  Vrs = [[
    [SOME @{term "\<lambda>(x::'a1, x2::'a2). {x}"}, NONE],
    [NONE, SOME @{term "\<lambda>(x::'a1, x2::'a2). {x2}"}]
  ]],
  tacs = [{
    Sb_Inj = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L1_def prod.map_id0}),
      resolve_tac ctxt [refl]
    ],
    Sb_comp_Injs = [],
    Sb_comp = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        (BNF_Def.map_comp0_of_bnf (the (BNF_Def.bnf_of @{context} "Product_Type.prod")) RS sym)
        :: @{thms Sb_L1_def id_apply}
      )),
      resolve_tac ctxt [refl]
    ],
    Vrs_Injs = [],
    Vrs_Sbs = [
      [SOME (fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Sb_L1_def case_prod_map_prod}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta UN_single}),
        resolve_tac ctxt [refl]
      ]), NONE],
      [NONE, SOME (fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Sb_L1_def case_prod_map_prod}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta UN_single}),
        resolve_tac ctxt [refl]
      ])]
    ],
    Sb_cong = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L1_def case_prod_beta}),
      resolve_tac ctxt @{thms prod.map_cong0},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms singletonI},
      hyp_subst_tac ctxt,
      assume_tac ctxt,
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      rotate_tac ~1,
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms singletonI},
      hyp_subst_tac ctxt,
      assume_tac ctxt
    ]
  } : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_axioms]
} : BMV_Monad_Def.bmv_monad_model;
\<close>
ML \<open>
val L1_bmv = fst (BMV_Monad_Def.bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) I model_L1 @{context})
\<close>

ML \<open>
val model_L2 = {
  ops = [@{typ "('a1, 'a2) L2"}],
  bd = @{term natLeq},
  var_class = @{class var},
  leader = 0,
  frees = [@{typ 'a1}, @{typ "'a2"}],
  lives = [],
  bmv_ops = [
    BMV_Monad_Def.morph_bmv_monad (
      MRBNF_Util.subst_typ_morphism (
        BMV_Monad_Def.frees_of_bmv_monad id_bmv ~~ [@{typ "'a1"}]
    )) id_bmv,
    BMV_Monad_Def.morph_bmv_monad (
      MRBNF_Util.subst_typ_morphism (
        BMV_Monad_Def.frees_of_bmv_monad id_bmv ~~ [@{typ "'a2"}]
    )) id_bmv,
    BMV_Monad_Def.morph_bmv_monad (
      MRBNF_Util.subst_typ_morphism (
        BMV_Monad_Def.frees_of_bmv_monad FType_bmv ~~ [@{typ "'a2::var"}]
    )) FType_bmv
  ],
  Maps = [NONE],
  Injs = [[@{term "id :: 'a1 \<Rightarrow> 'a1"}, @{term "id :: 'a2 \<Rightarrow> 'a2"}, @{term "TyVar :: 'a2::var \<Rightarrow> 'a2 FType"}]],
  Sbs = [@{term "Sb_L2 :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a1, 'a2::var) L2"}],
  Vrs = [[
    [SOME @{term "Vrs_L2_1 :: ('a1, 'a2::var) L2 \<Rightarrow> _"}, NONE],
    [NONE, SOME @{term "Vrs_L2_2 :: ('a1, 'a2::var) L2 \<Rightarrow> _"}],
    [NONE, SOME @{term "Vrs_L2_3 :: ('a1, 'a2::var) L2 \<Rightarrow> _"}]
  ]],
  tacs = [{
    Sb_Inj = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Sb_Inj_FType id_apply prod.map_id0}),
      resolve_tac ctxt [refl]
    ],
    Sb_comp_Injs = [],
    Sb_comp = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt (
        (BNF_Def.map_comp0_of_bnf (the (BNF_Def.bnf_of @{context} "Product_Type.prod")) RS sym)
        :: @{thms Sb_L2_def id_apply Sb_comp_FType[unfolded SSupp_FType_def tvVVr_tvsubst_FType_def[unfolded comp_def] tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric]]}
      )),
      resolve_tac ctxt [refl]
    ],
    Vrs_Injs = [],
    Vrs_Sbs = [
      [SOME (fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Vrs_L2_1_def case_prod_map_prod}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta UN_single id_apply}),
        resolve_tac ctxt [refl]
      ]), NONE],
      [NONE, SOME (fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Vrs_L2_2_def case_prod_map_prod}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta insert_is_Un[symmetric] UN_insert UN_empty Un_empty_right id_apply}),
        resolve_tac ctxt [refl]
      ])],
      [NONE, SOME (fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Vrs_L2_3_def case_prod_map_prod}),
        K (Local_Defs.unfold0_tac ctxt @{thms case_prod_beta UN_single id_apply}),
        resolve_tac ctxt @{thms Vrs_Sb_FType},
        K (Local_Defs.unfold0_tac ctxt @{thms SSupp_FType_def tvVVr_tvsubst_FType_def[unfolded comp_def] tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric]}),
        assume_tac ctxt
      ])]
    ],
    Sb_cong = fn ctxt => EVERY1 [
      K (Local_Defs.unfold0_tac ctxt @{thms Sb_L2_def Vrs_L2_1_def Vrs_L2_2_def Vrs_L2_3_def case_prod_beta id_apply}),
      resolve_tac ctxt @{thms prod.map_cong0},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms singletonI},
      hyp_subst_tac ctxt,
      assume_tac ctxt,
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      resolve_tac ctxt @{thms prod.map_cong0},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      hyp_subst_tac ctxt,
      rotate_tac ~2,
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms insertI1},
      assume_tac ctxt,
      hyp_subst_tac ctxt,
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      resolve_tac ctxt @{thms prod.map_cong0},
      eresolve_tac ctxt @{thms Basic_BNFs.fsts.cases},
      hyp_subst_tac ctxt,
      rotate_tac ~2,
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      resolve_tac ctxt @{thms insertI2},
      resolve_tac ctxt @{thms singletonI},
      assume_tac ctxt,
      eresolve_tac ctxt @{thms Basic_BNFs.snds.cases},
      hyp_subst_tac ctxt,
      resolve_tac ctxt @{thms Sb_cong_FType[unfolded SSupp_FType_def tvVVr_tvsubst_FType_def[unfolded comp_def] tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric]]},
      REPEAT_DETERM o assume_tac ctxt,
      rotate_tac ~2,
      dresolve_tac ctxt @{thms meta_spec},
      dresolve_tac ctxt @{thms meta_mp},
      assume_tac ctxt,
      assume_tac ctxt
    ]
  } : (Proof.context -> tactic) BMV_Monad_Def.bmv_monad_axioms]
} : BMV_Monad_Def.bmv_monad_model;
\<close>
ML \<open>
val L2_bmv = fst (BMV_Monad_Def.bmv_monad_def BNF_Def.Smart_Inline (K BNF_Def.Dont_Note) I model_L2 @{context})
\<close>

local_setup \<open>snd o BMV_Monad_Def.compose_bmv_monad I L_bmv [L1_bmv, L2_bmv]\<close>

end