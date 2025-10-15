theory Linearize
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_Recursor"
begin

(* This theory we start with an MRBNF F, which is assumed (in the imported theory 
Common_Data_Codata_Bindings) to have the following characteristics:
  ** is map-constrained to small-support endofunctions in the 1st position, 
  ** is map-constrained to small-support endobijections in the 2nd position,  
  ** is unconstrained in the 3rd and 4th position.   
We show that applying the nonrepetitiveness construction at the 3rd position (on which F is assumed 
to be pullback-preserving), we transform it into an MRBNF F' that has the same characteristics 
as F except that the 3rd position becomes map-constrained to small-support endobijections.  
*)

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV :: 'a set| then f else id"

typedecl ('a, 'b, 'c, 'd) F
consts map_F :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> ('b :: var \<Rightarrow> 'b) \<Rightarrow>
  ('c \<Rightarrow> 'c') \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('a, 'b, 'c, 'd) F \<Rightarrow> ('a, 'b, 'c', 'd') F"
consts set1_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'a set"
consts set2_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'b set"
consts set3_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'c set"
consts set4_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'd set"
consts rrel_F :: "('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> ('a, 'b, 'c', 'd') F \<Rightarrow> bool"

declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
mrbnf "('a :: var, 'b :: var, 'c, 'd) F"
  map: map_F
  sets: free: set1_F bound: set2_F live: set3_F live: set4_F
  bd: natLeq
  rel: rrel_F
  var_class: var
  sorry

(* we linearize this MRBNF on position 3*)
ML \<open>val lin_pos = 3\<close>

print_mrbnfs
declare [[ML_print_depth=10000]]
ML \<open>MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the \<close>

axiomatization where
  (* The next property assumes preservation of pullbacks on the third position. 
   NB: All MRBNFs already preserve _weak_ pullbacks, i.e., they satisfy the following property 
   without uniqueness.  *)
  F_rel_map_set2_strong: 
  "\<And> R S (x :: ('a :: var,'b :: var,'c,'d) F) y.
    rrel_F R S x y =
      (\<exists>!z. set3_F z \<subseteq> {(x, y). R x y} \<and>
            set4_F z \<subseteq> {(x, y). S x y} \<and> map_F id id fst fst z = x \<and> map_F id id snd snd z = y)"
  and
  (* The next property assumes that nonrepetitive elements exist: *)
  ex_nonrep: "\<exists>x. \<forall>x'. rrel_F top (=) x x' \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

abbreviation "rel_F \<equiv> mr_rel_F"

(* Important consequence of preservation of pullbacks (which is actually equivalent to it): 
The relator is closed under intersections. *)

ML \<open>
open BNF_Util BNF_Tactics MRBNF_Def

fun mk_F_strong_tac mrbnf F_map_id mr_rel_F_def F_mr_rel_mono_strong0 F_rel_map_set2_strong F_in_rel ctxt =
  let
    val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
    val var_types = var_types_of_mrbnf mrbnf;
    val nr_lives = length (filter (fn v => v = MRBNF_Def.Live_Var) var_types);
  in
    HEADGOAL (
      forward_tac ctxt [F_mr_rel_mono_strong0 OF flat (replicate 2 id_prems)] THEN_ALL_NEW (
        TRY o (rtac ctxt ballI THEN_ALL_NEW 
          resolve_tac ctxt [ballI, refl]) THEN_ALL_NEW
        TRY o (rtac ctxt impI THEN_ALL_NEW
          rtac ctxt (trans OF [@{thm top_apply} RS fun_cong, trans OF @{thms top_apply top_bool_def}])))) THEN
    unfold_thms_tac ctxt [F_map_id, mr_rel_F_def, @{thm eq_True}] THEN
    HEADGOAL (rotate_tac 2) THEN
    HEADGOAL (dtac ctxt (iffD1 OF [F_rel_map_set2_strong])) THEN
    unfold_thms_tac ctxt ([eqTrueI OF [subset_UNIV]] @ @{thms top_apply top_bool_def 
      Collect_const_case_prod if_True simp_thms(22)}) THEN
    unfold_thms_tac ctxt ([unfold_thms ctxt [id_apply, F_map_id, @{thm OO_Grp_alt}] (F_in_rel OF 
      id_prems), sym OF @{thms id_def}, mem_Collect_eq]) THEN
    HEADGOAL (etac ctxt exE) THEN
    HEADGOAL (etac ctxt exE) THEN
    HEADGOAL (etac ctxt @{thm alt_ex1E}) THEN
    REPEAT_DETERM_N (3+2*nr_lives) (HEADGOAL (etac ctxt conjE)) THEN
    HEADGOAL (Subgoal.FOCUS
      (fn {prems, context = ctxt, params, ...} => 
        HEADGOAL (Method.insert_tac ctxt [
          infer_instantiate' ctxt [SOME (snd (nth params 1)), SOME (snd (nth params 0))] (@{thm spec2} OF [nth prems 0]),
          infer_instantiate' ctxt [SOME (snd (nth params 2)), SOME (snd (nth params 0))] (@{thm spec2} OF [nth prems 0])] THEN_ALL_NEW
          etac ctxt impE THEN_ALL_NEW
          etac ctxt impE) THEN
        REPEAT_DETERM_N 3 (HEADGOAL (
          rtac ctxt conjI THEN_ALL_NEW
          rtac ctxt conjI THEN_ALL_NEW
          resolve_tac ctxt prems)) THEN
        HEADGOAL (rtac ctxt exI) THEN
        unfold_thms_tac ctxt @{thms inf_fun_def inf_bool_def} THEN
        HEADGOAL (rtac ctxt conjI) THEN
        HEADGOAL (Method.insert_tac ctxt prems) THEN
        HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
        REPEAT_DETERM_N nr_lives (HEADGOAL (EVERY' [
          TRY o rtac ctxt conjI,
          rtac ctxt @{thm subrelI},
          rtac ctxt CollectI,
          rtac ctxt @{thm case_prodI},
          rtac ctxt conjI THEN_ALL_NEW 
            etac ctxt (@{thm rev_subsetD} RS (iffD1 OF @{thms prod_in_Collect_iff})),
        assume_tac ctxt,
        assume_tac ctxt])) THEN
        HEADGOAL (rtac ctxt conjI THEN_ALL_NEW resolve_tac ctxt prems)
      ) ctxt)
  end
\<close>

(* lin_pos independent *)
lemma F_strong:
  "rel_F id id R3 R4 x y \<Longrightarrow> rel_F id id Q3 Q4 x y \<Longrightarrow> rel_F id id (inf R3 Q3) (inf R4 Q4) x y"
  apply (tactic \<open>mk_F_strong_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm F.map_id} 
    @{thm mr_rel_F_def} @{thm F.mr_rel_mono_strong0} @{thm F_rel_map_set2_strong} @{thm F.in_rel} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)

  apply (frule F.mr_rel_mono_strong0[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound];
      ((rule ballI, rule ballI refl)?, 
        (rule impI, rule trans[OF top_apply[THEN fun_cong] trans[OF top_apply top_bool_def]])?)) 
  thm trans[OF top_apply[THEN fun_cong] trans[OF top_apply top_bool_def]]
  apply(rotate_tac 2)
  apply (unfold F.map_id mr_rel_F_def eq_True)
  thm F_rel_map_set2_strong
  apply (drule F_rel_map_set2_strong[THEN iffD1])
  apply (unfold top_apply top_bool_def Collect_const_case_prod if_True eqTrueI[OF subset_UNIV] simp_thms(22))
  apply (unfold F.in_rel[OF supp_id_bound bij_id supp_id_bound, unfolded id_apply F.map_id OO_Grp_alt]
      id_def[symmetric] mem_Collect_eq)
  apply (elim exE alt_ex1E)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule conjE)
  subgoal premises subprems for z l r
    thm subprems
    apply (insert spec2[OF subprems(1), of r z]
        spec2[OF subprems(1), of l z]; (erule impE); (erule impE))
       apply (rule conjI; rule conjI; rule subprems)
       apply (rule conjI; rule conjI; rule subprems)
       apply (rule conjI; rule conjI; rule subprems)
    apply (rule exI)
    apply (unfold inf_fun_def inf_bool_def)
    apply (rule conjI)
     apply (insert subprems) []
     apply (hypsubst_thin)
    apply ((rule conjI)?,
        rule subrelI, 
        rule CollectI, 
        rule case_prodI, 
        (rule conjI; erule rev_subsetD[THEN iffD1[OF prod_in_Collect_iff]]),
        assumption, assumption)+
    apply (rule conjI)
    apply (rule subprems)+
    done
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rel_F_exchange_tac mrbnf F_mr_rel_mono_strong0 F_strong ctxt =
  let
    val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
  in
    HEADGOAL (Subgoal.FOCUS
      (fn {prems, context = ctxt, ...} => 
        HEADGOAL (EVERY' [
          rtac ctxt (F_mr_rel_mono_strong0 OF flat (replicate 2 id_prems)),
          rtac ctxt (F_strong OF prems),
          K (unfold_thms_tac ctxt ([id_apply, eqTrueI OF [refl]] @ @{thms ball_triv inf_apply inf_bool_def}))
        ]) THEN
        ALLGOALS (
          (rtac ctxt impI THEN' 
          rtac ctxt TrueI) ORELSE'
          (rtac ctxt ballI THEN' 
          rtac ctxt ballI THEN'
          rtac ctxt impI THEN'
          eresolve_tac ctxt [conjunct1, conjunct2]))
       ) ctxt)
  end
\<close>

(* lin_pos dependent? *)
(* Another important consequence: the following "exchange"-property, which could be read: 
Since the atoms have a fixed position, we can permute the relations: *)
lemma rel_F_exchange: 
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and x' :: "('a1,'a2,'a3','a4') F"
  assumes "rel_F id id R3 R4 x x'" and "rel_F id id Q3 Q4 x x'"
  shows "rel_F id id R3 Q4 x x'" 
  using assms apply -
  apply (tactic \<open>mk_rel_F_exchange_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) 
    @{thm F.mr_rel_mono_strong0} @{thm F_strong} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (rule F.mr_rel_mono_strong0[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound])
    apply (rule F_strong[OF prems])
       apply (unfold id_apply eqTrueI[OF refl] ball_triv inf_apply inf_bool_def)
       apply (intro impI TrueI)+
     apply (intro ballI impI; erule conjunct1 conjunct2)+
    done
  done

(* Then notion of two items having the same shape (w.r.t. the 3rd position): *)
(* these definitions are lin_pos dependent *)
definition sameShape1 :: "('a1::var,'a2::var,'a3,'a4) F \<Rightarrow> ('a1,'a2,'a3,'a4) F \<Rightarrow> bool" where 
  "sameShape1 x x' \<equiv> rel_F id id top (=) x x'"

definition nonrep2 :: "('a1::var,'a2::var,'a3,'a4) F \<Rightarrow> bool" where 
  "nonrep2 x \<equiv> \<forall> x'. sameShape1 x x' \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

ML\<open>
open BNF_Util BNF_Tactics

fun mk_nonrep2_map_F_tac mrbnf nonrep_def sameShape_def F_map_comp F_mr_rel_map mr_rel_F_def F_rel_compp 
  F_rel_Grp F_map_id F_in_rel F_rel_maps F_rel_refl_strong ctxt = 
  HEADGOAL (Subgoal.FOCUS 
    (fn {prems, context = ctxt, ...} => 
      let
        val var_types = var_types_of_mrbnf mrbnf;
        val nr_lives = length (filter (fn v => v = MRBNF_Def.Live_Var) var_types);
        val nr_non_lives = length (filter (fn v => not (v = MRBNF_Def.Live_Var)) var_types);
        val lin_live_pos = fold_index (fn (i, v) => fn b => 
          if (v = MRBNF_Def.Live_Var andalso i+1 < lin_pos) then b+1 else b) var_types 1;
        val switch_poses = map_range (fn i => if i < (lin_pos-(lin_live_pos)) then i+1 else i+2) (nr_non_lives);
        val switch = (fn thm1 => (fn thm2 => trans OF [thm1, thm2 RS sym]));
        val o_id = @{thm o_id};
        val id_o = @{thm id_o};
      in
        unfold_thms_tac ctxt [nonrep_def, sameShape_def] THEN
        HEADGOAL (EVERY' [
          rtac ctxt allI,
          rtac ctxt impI,
          etac ctxt exE,
          EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          K (unfold_thms_tac ctxt [switch id_o o_id]),
          EqSubst.eqsubst_tac ctxt [lin_pos] [switch o_id id_o], (*move all id to the right except for lin_pos*)
          EqSubst.eqsubst_tac ctxt [0] [F_map_comp RS sym] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          dtac ctxt (rotate_prems ~1 (F_mr_rel_map RS iffD1)) THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          K (unfold_thms_tac ctxt [switch id_o o_id, @{thm Grp_UNIV_id}]),
          K (unfold_thms_tac ctxt [switch @{thm OO_eq} @{thm eq_OO}]),  
          EqSubst.eqsubst_asm_tac ctxt [lin_live_pos] [switch @{thm eq_OO} @{thm OO_eq}], (*move all (=) to the left except for lin_live_pos*)
          K (unfold_thms_tac ctxt @{thms eq_alt}),   
          EqSubst.eqsubst_tac ctxt [0] @{thms Grp_UNIV_id}
        ]) THEN
        unfold_thms_tac ctxt [mr_rel_F_def, o_id, F_rel_compp, F_rel_Grp] THEN
        unfold_thms_tac ctxt [eqTrueI OF @{thms subset_UNIV}, @{thm simp_thms(21)}, id_o, @{thm UNIV_def} RS sym] THEN
        unfold_thms_tac ctxt ([eqTrueI OF [@{thm UNIV_I}], id_apply] @ @{thms Grp_UNIV_id OO_def Grp_def simp_thms(21)}) THEN
        HEADGOAL (EVERY' [
          etac ctxt exE,
          etac ctxt conjE,
          dtac ctxt (rotate_prems ~1 (F_in_rel RS iffD1)) THEN_ALL_NEW
            TRY o resolve_tac ctxt prems,
          Method.insert_tac ctxt [unfold_thms ctxt [nonrep_def, sameShape_def, mr_rel_F_def, F_map_id] 
            (nth prems (length prems -1))],
          etac ctxt exE,
          etac ctxt conjE,
          etac ctxt CollectE,
          etac ctxt conjE
        ]) THEN
        REPEAT_DETERM_N (nr_lives-1) (HEADGOAL (
          etac ctxt conjE)) THEN
        HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
        HEADGOAL (Subgoal.FOCUS 
          (fn {prems = subprems, context = ctxt, params, ...} => 
            HEADGOAL (EVERY' [
              Method.insert_tac ctxt [nth subprems 0],
              etac ctxt allE,
              etac ctxt impE,
              rtac ctxt (infer_instantiate' ctxt [NONE, SOME (snd (nth params 1))] exI),
              EqSubst.eqsubst_tac ctxt [1] [nth F_rel_maps 0],
              EqSubst.eqsubst_tac ctxt [1] [nth F_rel_maps 1]
            ]) THEN
            HEADGOAL (rtac ctxt F_rel_refl_strong) THEN
            REPEAT_DETERM_N nr_lives (HEADGOAL (
                (dresolve_tac ctxt (map (fn p => subsetD OF [p] RS @{thm Collect_case_prodD}) (drop 1 subprems)) THEN'
                  (assume_tac ctxt ORELSE' 
                  (rtac ctxt sym THEN' assume_tac ctxt))))) THEN
            HEADGOAL (EVERY' [
              etac ctxt exE,
              EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
              EqSubst.eqsubst_tac ctxt switch_poses [switch id_o o_id],
              EqSubst.eqsubst_tac ctxt [0] [F_map_comp RS sym] THEN_ALL_NEW
                TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
              rtac ctxt exI,
              dtac ctxt arg_cong,
              assume_tac ctxt
            ]) 
          ) ctxt)
      end)
  ctxt)
\<close>

lemma nonrep2_map_F:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|"  and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 x"
  shows "nonrep2 (map_F v u id g x)"
  using assms apply -
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)
    apply (subst F.map_comp; (rule prems bij_id supp_id_bound)?)
    apply (unfold o_id id_o)
    apply (drule iffD1[OF F.mr_rel_map(1), rotated -1]; (rule prems bij_id supp_id_bound)?)
    apply (unfold trans[OF id_o o_id[symmetric]] Grp_UNIV_id trans[OF OO_eq eq_OO[symmetric]])
    apply (unfold trans[OF eq_OO OO_eq[symmetric], of top])
    apply (unfold eq_alt)
    apply (subst Grp_UNIV_id)
    apply (unfold mr_rel_F_def o_id F.rel_compp F.rel_Grp)
    apply (unfold eqTrueI[OF subset_UNIV] simp_thms(21) UNIV_def[symmetric] id_o)
    apply (unfold Grp_UNIV_id OO_def Grp_def eqTrueI[OF UNIV_I] simp_thms(21) id_apply)
    apply (unfold id_def[THEN sym])
    apply (erule exE)
    apply (erule conjE)
    apply (drule F.in_rel[THEN iffD1, rotated -1]; (rule prems)?)
    apply (erule exE)
    apply (erule conjE)
    apply (erule CollectE)
    apply (erule conjE)
    apply (erule conjE)
    apply (insert prems(4)[unfolded nonrep2_def sameShape1_def mr_rel_F_def F.map_id])
    apply (rotate_tac -1)
    apply (hypsubst_thin)
    subgoal premises subprems for x' y z
      apply (insert subprems(1))
      apply (erule allE)
      apply (erule impE)
       apply (subst F.rel_map)
       apply (subst F.rel_map)
       apply (rule F.rel_refl_strong)
        apply (drule subsetD[OF subprems(2), THEN Collect_case_prodD] 
          subsetD[OF subprems(3), THEN Collect_case_prodD]; 
          (assumption)?; (rule sym; assumption)?)+
      apply (elim exE)
      apply (subst F.map_comp[OF _ _ _ supp_id_bound bij_id supp_id_bound, unfolded trans[OF id_o o_id[symmetric]]]; (rule prems)?)
      apply (subst F.map_comp[THEN sym]; (rule prems bij_id supp_id_bound)?)
      subgoal premises subprems for f
        apply (rule exI[of _ f]) (* instantiation not necessary but easy*)
        apply (subst subprems)
        apply (subst F.map_comp; (rule prems bij_id supp_id_bound)?)
        apply (unfold o_id id_o)
        apply (rule refl)
        done
      done
    done
  done

ML\<open>
open BNF_Util BNF_Tactics

fun mk_nonrep2_map_F_rev_tac mrbnf nonrep_def sameShape_def F_mr_rel_map1 F_mr_rel_map2 F_mr_rel_map3 F_map_comp F_rel_eq 
  F_mr_rel_id rel_F_exchange F_mr_rel_flip F_mr_rel_mono_strong0 F_mr_rel_Grp ctxt = 
  HEADGOAL (Subgoal.FOCUS 
    (fn {prems, context = ctxt, ...} => 
      let
        val var_types = var_types_of_mrbnf mrbnf;
        val nr_lives = length (filter (fn v => v = MRBNF_Def.Live_Var) var_types);
        val nr_non_lives = length (filter (fn v => not (v = MRBNF_Def.Live_Var)) var_types);
        val lin_live_pos = fold_index (fn (i, v) => fn b => 
          if (v = MRBNF_Def.Live_Var andalso i+1 < lin_pos) then b+1 else b) var_types 1;
        val switch = (fn thm1 => (fn thm2 => trans OF [thm1, thm2 RS sym]));
      in
        unfold_thms_tac ctxt [nonrep_def, sameShape_def] THEN
        HEADGOAL (EVERY' [
          rtac ctxt allI,
          rtac ctxt impI,
          etac ctxt exE,
          forward_tac ctxt [rotate_prems ~1 F_mr_rel_map2] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          rotate_tac 1,
          EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) nr_non_lives) [switch @{thm o_id} @{thm id_o}],
          EqSubst.eqsubst_asm_tac ctxt [lin_live_pos] @{thms Grp_UNIV_id},
          K (unfold_thms_tac ctxt [switch @{thm eq_OO} @{thm OO_eq}]),
          EqSubst.eqsubst_asm_tac ctxt [lin_live_pos] [switch @{thm OO_eq} @{thm eq_OO}], (*move all (=) to the right and then lin_live_pos back*)
          EqSubst.eqsubst_asm_tac ctxt [lin_live_pos] @{thms eq_alt},
          EqSubst.eqsubst_asm_tac ctxt [0] [F_mr_rel_map1 RS sym] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          Method.insert_tac ctxt [unfold_thms ctxt [nonrep_def, sameShape_def] (nth prems (length prems - 1))],
          etac ctxt allE,
          etac ctxt impE,
          rtac ctxt exI,
          assume_tac ctxt,
          etac ctxt thin_rl,
          etac ctxt exE,
          EqSubst.eqsubst_asm_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          K (unfold_thms_tac ctxt @{thms id_o o_id}),
          EqSubst.eqsubst_asm_tac ctxt [1] [F_rel_eq RS sym],
          EqSubst.eqsubst_asm_tac ctxt [1] [F_mr_rel_id],
          dtac ctxt (rotate_prems ~1 (iffD1 OF [F_mr_rel_map1])) THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          K (unfold_thms_tac ctxt @{thms id_o OO_eq}),
          dtac ctxt (rotate_prems 1 rel_F_exchange),
          rtac ctxt (F_mr_rel_flip RS iffD1) THEN_ALL_NEW
            TRY o resolve_tac ctxt @{thms supp_id_bound bij_id},
          K (unfold_thms_tac ctxt @{thms inv_id}),
          EqSubst.eqsubst_asm_tac ctxt [0] [F_mr_rel_map3] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (2 * nr_lives)) @{thms Grp_def},
          EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_non_lives)) @{thms inv_o_simp1} THEN_ALL_NEW
            TRY o resolve_tac ctxt (@{thm bij_id}::prems),
          K (unfold_thms_tac ctxt ((eqTrueI OF @{thms UNIV_I}):: @{thms id_apply simp_thms(21)})),
          EqSubst.eqsubst_asm_tac ctxt [lin_live_pos] @{thms eq_commute},
          K (unfold_thms_tac ctxt @{thms eq_OO conversep_def}),
          etac ctxt (rotate_prems (~1 - (length var_types)) F_mr_rel_mono_strong0) THEN_ALL_NEW
            TRY o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ]) THEN
        REPEAT_DETERM_N (length var_types) (
          (HEADGOAL (
            (* for bound and free *)
            rtac ctxt ballI THEN'
            rtac ctxt refl)) 
          ORELSE 
          (HEADGOAL (
            (* for lives*)
            rtac ctxt ballI THEN'
            rtac ctxt ballI THEN'
            rtac ctxt impI THEN'
            rotate_tac 2 THEN'
            EqSubst.eqsubst_asm_tac ctxt [0] @{thms eq_commute} THEN'
            assume_tac ctxt))
        ) THEN
        HEADGOAL (EVERY' [
          etac ctxt thin_rl,
          EqSubst.eqsubst_asm_tac ctxt [lin_live_pos] [@{thm Grp_UNIV_def} RS sym],
          rtac ctxt exI,
          EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_lives -1)) @{thms eq_alt},
          EqSubst.eqsubst_asm_tac ctxt [0] [F_mr_rel_Grp] THEN_ALL_NEW
            TRY o resolve_tac ctxt @{thms supp_id_bound bij_id}
        ]) THEN
        unfold_thms_tac ctxt ([eqTrueI OF @{thms subset_UNIV}, eqTrueI OF @{thms UNIV_I}, @{thm UNIV_def} RS sym] @ 
          @{thms simp_thms(21) Grp_def}) THEN
        HEADGOAL (assume_tac ctxt)
      end)
  ctxt)
\<close>

(* Here we need pullback preservation: *)
lemma nonrep2_map_F_rev:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'a4'"
  assumes u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 (map_F id u id g x)"
  shows "nonrep2 x"
  using assms apply -
 (* apply (tactic \<open>mk_nonrep2_map_F_rev_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm nonrep2_def} @{thm sameShape1_def} @{thm F.mr_rel_map(1)}
    @{thm F.mr_rel_map(2)} @{thm F.mr_rel_map(3)} @{thm F.map_comp} @{thm F.rel_eq} @{thm F.mr_rel_id} @{thm rel_F_exchange} 
    @{thm F.mr_rel_flip} @{thm F.mr_rel_mono_strong0} @{thm F.mr_rel_Grp} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)*)
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)

(* alt *)
    apply (insert prems(3)[unfolded nonrep2_def sameShape1_def]) (*lastprem*)
    apply (elim allE impE)
     apply (rule F.mr_rel_map(1)[THEN iffD2]; (rule prems supp_id_bound bij_id)?)
  (*_ * (2*nr_BF + nr_As + 2(x,y)) *)
   apply (drule F.mr_rel_map(2)[rotated -1, of _ _ _ _ _ _ _ _ id _]; (rule prems supp_id_bound bij_id)?)
     apply (unfold o_id id_o Grp_UNIV_id eq_OO OO_eq)
     apply (assumption)
(*
    apply (rotate_tac)
    apply (subst (asm) (1 2) trans[OF o_id id_o[symmetric]]) (*1..nr_non_lives*)
    apply (subst (asm) (1) Grp_UNIV_id) (*lin_live_pos*)
    apply (unfold trans[OF eq_OO OO_eq[symmetric]])
    apply (subst (asm) (1) trans[OF OO_eq eq_OO[symmetric]]) (*lin_live_pos*)
    apply (subst (asm) (1) eq_alt) (*lin_live_pos*)
    thm eq_alt Grp_UNIV_id trans[OF OO_eq eq_OO[symmetric]]
    apply (subst (asm) F.mr_rel_map(1)[symmetric]; (rule prems supp_id_bound bij_id)?)
     apply (assumption)
*)

    apply (erule exE)
    apply (subst (asm) F.map_comp; (rule prems supp_id_bound bij_id)?)
    apply (unfold o_id id_o)

    thm F.map_cong

    apply (subst (asm) F.rel_eq[symmetric])
    apply (unfold F.mr_rel_id)
    thm F.mr_rel_map
    apply (drule iffD1[OF F.mr_rel_map(1), rotated -1]; (rule prems supp_id_bound bij_id)?)
    apply (unfold id_o OO_eq)
    thm rel_F_exchange[rotated]
    apply (drule rel_F_exchange[rotated])
     apply (rule iffD1[OF F.mr_rel_flip]; (rule supp_id_bound bij_id)?)
    apply (unfold inv_id)
     apply (subst (asm) F.mr_rel_map(3); (rule prems supp_id_bound bij_id)?)
     apply ((*subst (asm) (1 2 3 4)*) unfold Grp_def) (*TWICE for all lives *)
    apply (subst (asm) (1 2) inv_o_simp1; (rule prems bij_id)?) (*for all frees and bounds*)
     apply (tactic \<open>unfold_thms_tac @{context} @{thms eqTrueI[OF UNIV_I] simp_thms(21) id_apply}\<close>) (*for all frees*)
     apply (subst (asm) (1) eq_commute) (*lin_live_pos*)
     apply (unfold eq_OO conversep_def)
     apply (elim F.mr_rel_mono_strong0[rotated -5]; (rule supp_id_bound bij_id)?) (*- len vartypes - 1*)
      (*left subtactic is for frees and bounds, right subtactic for lives*)
    apply ((rule ballI,rule refl)?; (rule ballI,rule ballI,rule impI,rotate_tac 2,subst (asm) eq_commute,assumption))+

    apply (erule thin_rl)
    apply (subst (asm) (1) Grp_UNIV_def[symmetric]) (*lin_live_pos*)
    apply (rule exI)
    apply (subst (asm) (1) eq_alt) (* repeat lives - 1 *)
    thm F.mr_rel_Grp
    apply (subst (asm) F.mr_rel_Grp; (rule supp_id_bound bij_id)?)
    apply (unfold eqTrueI[OF subset_UNIV] eqTrueI[OF UNIV_I] UNIV_def[THEN sym] simp_thms(21) Grp_def)
    apply (assumption)
    done
  done

ML\<open>
open BNF_Util BNF_Tactics
fun mk_nonrep2_map_bij_tac nonrep_def sameShape_def F_mr_rel_map1 F_map_comp cgs ctxt = 
  HEADGOAL (Subgoal.FOCUS 
    (fn {prems, context = ctxt, ...} => 
      unfold_thms_tac ctxt [nonrep_def, sameShape_def] THEN
      HEADGOAL (EVERY' [
        rtac ctxt allI,
        rtac ctxt impI,
        dtac ctxt (rotate_prems ~1 (F_mr_rel_map1 RS iffD1)) THEN_ALL_NEW
          TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
        K (unfold_thms_tac ctxt @{thms o_id Grp_UNIV_id eq_OO Grp_OO_top}),
        dtac ctxt (Object_Logic.rulify ctxt (unfold_thms ctxt [nonrep_def, sameShape_def] (nth prems 1))),
        etac ctxt exE,
        hyp_subst_tac_thin true ctxt
      ]) THEN
      unfold_thms_tac ctxt @{thms triv_forall_equality} THEN
      HEADGOAL (Subgoal.FOCUS 
        (fn {context = ctxt, params, ...} => 
          HEADGOAL (EVERY' (map (fn ((_, cf), cg) => 
            let
              val g = Thm.term_of cg
              val (dom_g, rng_g) = fastype_of g |> dest_funT
              val inv_g = Const ("Hilbert_Choice.inv", 
                (fastype_of g) --> (rng_g --> dom_g)) $ g
              val f_o_inv_g = HOLogic.mk_comp (Thm.term_of cf, inv_g)
            in
              rtac ctxt (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt f_o_inv_g)] exI) 
            end) (params ~~ cgs))
          ) THEN
          HEADGOAL (rtac ctxt sym) THEN
          HEADGOAL (rtac ctxt trans) THEN
          HEADGOAL (rtac ctxt F_map_comp THEN_ALL_NEW
            TRY o resolve_tac ctxt @{thms bij_id supp_id_bound}) THEN
          unfold_thms_tac ctxt ([@{thm inv_o_simp1} OF (take 1 prems), @{thm o_assoc} RS sym] @ @{thms id_o o_id}) THEN
          HEADGOAL (rtac ctxt refl)
        ) ctxt)
  ) ctxt)
\<close>

lemma nonrep2_mapF_bij:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and g::"'a3\<Rightarrow>'a3"
  assumes g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F id id g id x)" (is "nonrep2 ?x'")
  using assms apply -
  apply (tactic \<open>mk_nonrep2_map_bij_tac @{thm nonrep2_def}
    @{thm sameShape1_def} @{thm F.mr_rel_map(1)} @{thm F.map_comp} [@{cterm g}] @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>) 
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)
    apply (drule F.mr_rel_map(1)[THEN iffD1, rotated -1]; (rule supp_id_bound bij_id)?)
    apply (unfold o_id Grp_UNIV_id eq_OO Grp_OO_top)
    apply (drule x[unfolded nonrep2_def sameShape1_def, rule_format])
    apply (erule exE conjE)+
    apply hypsubst_thin
    subgoal for _ f
      apply (rule exI[of _ "f o inv g"])
      apply (rule sym)
      apply (rule trans)
       apply (rule F.map_comp; (rule supp_id_bound bij_id)?)
      apply (unfold id_o o_id inv_o_simp1[OF g] o_assoc[symmetric])
      apply (rule refl)
      done
    done
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_nonrep2_mapF_bij_2_tac mrbnf nonrep2_mapF_bij nonrep2_map_F F_map_comp ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
    let val nr_prems = length prems;
        val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
    in
      HEADGOAL (rtac ctxt (unfold_thms ctxt ((F_map_comp OF ((take (nr_prems-2) prems) @ id_prems)) :: @{thms id_o o_id}) 
        (nonrep2_mapF_bij OF [nth prems (nr_prems-2), nonrep2_map_F OF (nth_drop (nr_prems-2) prems)])
      ))
     end) ctxt)
\<close>

lemma nonrep2_mapF_bij_2:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g::"'a3\<Rightarrow>'a3" and f::"'a4\<Rightarrow>'a4'"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|" and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|"
    and g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F v u g f x)" 
  using assms apply -
  apply (tactic \<open>mk_nonrep2_mapF_bij_2_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) 
    @{thm nonrep2_mapF_bij} @{thm nonrep2_map_F} @{thm F.map_comp} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (rule nonrep2_mapF_bij[OF prems(4) nonrep2_map_F[OF prems(1,2,3,5)], 
          unfolded F.map_comp[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound] id_o o_id])
    done
  done


typedef ('a1::var,'a2::var,'a3::var,'a4) F' = "{x :: ('a1,'a2,'a3,'a4) F. nonrep2 x}"
  apply (unfold mem_Collect_eq nonrep2_def sameShape1_def mr_rel_F_def F.map_id)
  by (rule ex_nonrep)

definition set1_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a1 set" where "set1_F' = set1_F o Rep_F'"
definition set2_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a2 set" where "set2_F' = set2_F o Rep_F'"
definition set3_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a3 set" where "set3_F' = set3_F o Rep_F'"
definition set4_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a4 set" where "set4_F' = set4_F o Rep_F'"

definition map_F' :: "('a1::var \<Rightarrow> 'a1) \<Rightarrow> ('a2::var \<Rightarrow> 'a2) \<Rightarrow> ('a3::var \<Rightarrow> 'a3) \<Rightarrow> ('a4 \<Rightarrow> 'a4') 
  \<Rightarrow> ('a1,'a2,'a3,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F'"
  where "map_F' v u f g = Abs_F' o map_F (asSS v) (asSS (asBij u)) (asBij f) g o Rep_F'"

definition rrel_F' :: "('a4 \<Rightarrow> 'a4' \<Rightarrow> bool) \<Rightarrow> ('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F' \<Rightarrow> bool"
  where "rrel_F' R x x' = rrel_F (=) R (Rep_F' x) (Rep_F' x')"

(* Verifying the axioms of a MRBNF for F':  *)
lemma F'_map_id: "map_F' id id id id = id"
  apply (unfold map_F'_def asSS_def asBij_def 
      eqTrueI[OF bij_id] eqTrueI[OF supp_id_bound] if_True)
  apply (rule ext)
  apply (unfold o_apply F.map_id Rep_F'_inverse)
  apply (unfold id_def)
  apply (rule refl)
  done

lemma F'_map_comp1_:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  shows "map_F' (v1 o u1) (v2 o u2) (v3 o u3) (g o f) = map_F' v1 v2 v3 g o map_F' u1 u2 u3 f"
  using assms apply -
  subgoal premises prems
    apply (unfold map_F'_def asBij_def asSS_def)
    apply (unfold eqTrueI[OF bij_comp[OF prems (3, 5)]] eqTrueI[OF bij_comp[OF prems (7, 9)]] 
        eqTrueI[OF supp_comp_bound[OF prems(1,2) infinite_UNIV]] eqTrueI[OF supp_comp_bound[OF prems(4,6) infinite_UNIV]]
        if_True)
    apply (unfold 
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] eqTrueI[OF assms(5)] eqTrueI[OF assms(6)]
        eqTrueI[OF assms(7)] eqTrueI[OF assms(8)] eqTrueI[OF assms(9)] eqTrueI[OF assms(10)]
        if_True)
    apply (rule ext)
    apply (subst F.map_comp0; (rule prems)?)
    apply (unfold o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
     apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
    apply (rule refl)
    done
  done


(* This tactic is applicable to all 4 of the following <F'_setx_map_> lemmas*)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_set_map_tac set_F'_def map_F'_def Abs_F'_inverse Rep_F' nonrep2_mapF_bij_2 F_set_map ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems, context = ctxt, ...} =>
      unfold_thms_tac ctxt ([set_F'_def, map_F'_def] @ map (fn thm => thm RS eqTrueI) prems @
        @{thms asSS_def asBij_def if_True o_apply}) THEN
      HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
        rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems),
        rtac ctxt F_set_map THEN_ALL_NEW
          resolve_tac ctxt prems])
    ) ctxt)
\<close>

lemma F'_set1_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set1_F' (map_F' u1 u2 u3 f b) = u1 ` set1_F' b"
  using assms apply -
  apply (tactic \<open>mk_set_map_tac @{thm set1_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(1)} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold set1_F'_def map_F'_def asSS_def asBij_def
        eqTrueI[OF prems(1)] eqTrueI[OF prems(2)] eqTrueI[OF prems(3)] eqTrueI[OF prems(4)] eqTrueI[OF prems(5)] o_apply if_True)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
     apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
    apply (rule F.set_map(1); (rule prems))
    done
  done

lemma F'_set2_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set2_F' (map_F' u1 u2 u3 f b) = u2 ` set2_F' b"
  using assms apply -
  apply (tactic \<open>mk_set_map_tac @{thm set2_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(2)} @{context}\<close>)
  done

lemma F'_set3_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set3_F' (map_F' u1 u2 u3 f b) = u3 ` set3_F' b"
  using assms apply -
  apply (tactic \<open>mk_set_map_tac @{thm set3_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(3)} @{context}\<close>)
  done

lemma F'_set4_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set4_F' (map_F' u1 u2 u3 f b) = f ` set4_F' b"
  using assms apply -
  apply (tactic \<open>mk_set_map_tac @{thm set4_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(4)} @{context}\<close>)
  done

lemma F'_map_cong_[fundef_cong]:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
    and "\<forall> a \<in> set1_F' x. u1 a = v1 a"
    and "\<forall> a \<in> set2_F' x. u2 a = v2 a"
    and "\<forall> a \<in> set3_F' x. u3 a = v3 a"
    and "\<forall> a \<in> set4_F' x. f a = g a"
  shows "map_F' u1 u2 u3 f x = map_F' v1 v2 v3 g x"
  using assms apply -
  subgoal premises prems
    apply (unfold map_F'_def asSS_def asBij_def 
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] eqTrueI[OF assms(5)] 
        eqTrueI[OF assms(6)] eqTrueI[OF assms(7)] eqTrueI[OF assms(8)] eqTrueI[OF assms(9)] eqTrueI[OF assms(10)]
        eqTrueI[OF assms(11)] eqTrueI[OF assms(12)] eqTrueI[OF assms(13)] eqTrueI[OF assms(14)] if_True o_apply)
    apply (subst F.map_cong; (rule prems(14,13,12,11,10,9,8,7,6,5,4,3,2,1))?) (*reverse prems so that the v-prems apply before the u-prems*)
         apply (rule refl)
         apply (erule bspec[OF prems(11)[unfolded set1_F'_def o_apply]] 
        bspec[OF prems(12)[unfolded set2_F'_def o_apply]]
        bspec[OF prems(13)[unfolded set3_F'_def o_apply]]
        bspec[OF prems(14)[unfolded set4_F'_def o_apply]])+
    apply (rule refl)
    done
  done

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o natLeq"
  apply (unfold set1_F'_def o_apply)
  by (rule F.set_bd(1))

lemma F'_set2_bd: "\<And>b. |set2_F' b| <o natLeq"
  apply (unfold set2_F'_def o_apply)
  by (rule F.set_bd(2))

lemma F'_set3_bd: "\<And>b. |set3_F' b| <o natLeq"
  apply (unfold set3_F'_def o_apply)
  by (rule F.set_bd(3))

lemma F'_set4_bd: "\<And>b. |set4_F' b| <o natLeq"
  apply (unfold set4_F'_def o_apply)
  by (rule F.set_bd(4))

lemma F'_rel_comp_leq_: "rrel_F' Q OO rrel_F' R \<le> rrel_F' (Q OO R)"
  apply (rule predicate2I)
  apply (erule relcomppE)
  apply (unfold rrel_F'_def)
  subgoal premises prems for x y b
    apply (insert prems(1))
    apply (drule relcomppI[of _ "Rep_F' x" "Rep_F' b" _ "Rep_F' y"])
     apply (rule prems(2))
    apply (unfold F.rel_compp[symmetric] eq_OO)
    apply (assumption)
    done
  done

lemma rrel_F_map_F3:
  fixes x :: "('a :: var,'b :: var,'c,'d) F"
  shows "rrel_F (Grp (f :: 'c \<Rightarrow> 'c)) R x y = rrel_F (=) R (map_F id id f id x) y"
  apply (unfold F.rel_map(1) Grp_def id_apply eqTrueI[OF UNIV_I] simp_thms(21))
  apply (rule iffI)
   apply (erule F.rel_mono_strong; (assumption?, (erule sym)?))+
  done

lemma F'_in_rel:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes u1: "|supp u1| <o |UNIV :: 'a1 set|"
    and u2: "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" 
    and u3: "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "rrel_F' R (map_F' u1 u2 u3 id x) y =
    (\<exists>z. set4_F' z \<subseteq> {(x, y). R x y} \<and> map_F' id id id fst z = x \<and> map_F' u1 u2 u3 snd z = y)"
  using assms apply -
  subgoal premises prems
    apply (unfold rrel_F'_def set4_F'_def map_F'_def asSS_def asBij_def if_True 
        eqTrueI[OF prems(1)] eqTrueI[OF prems(2)] eqTrueI[OF prems(3)] eqTrueI[OF prems(4)] 
        eqTrueI[OF prems(5)]
        eqTrueI[OF supp_id_bound] eqTrueI[OF bij_id] o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
     apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)

(* instantiation for bounds B, frees F, lives A: [_ * nr_BFs @ id * nr_BFs @ _ * nr_As @ id * nr_As] *)
    apply (subst F.map_comp[of _ _ id id _ _ id id, unfolded o_id id_o, symmetric]; (rule prems bij_id supp_id_bound)?)
    apply (subst rrel_F_map_F3[symmetric])
    apply (subst F.in_rel; (rule prems)?)

    apply (rule iffI)
    apply (unfold Grp_def eqTrueI[OF UNIV_I] simp_thms(21))
     apply (erule exE)
     apply (erule conjE)
     apply (erule conjE)
     apply (erule CollectE)
     apply (erule conjE)
    subgoal premises subprems for z
   apply (rule exI[of _ "(Abs_F' (map_F id id fst id z))"])
      apply ((subst Abs_F'_inverse[unfolded mem_Collect_eq]), (tactic \<open>defer_tac 1\<close>))+ 
         apply (tactic \<open>distinct_subgoals_tac\<close>)
      prefer 2
       apply (rule nonrep2_map_F_rev; (rule bij_id supp_id_bound)?)
       apply (subst F.map_comp; (rule bij_id supp_id_bound)?)
       apply (unfold o_id id_o)
       apply (subst subprems)
      apply (rule Rep_F'[unfolded mem_Collect_eq])

      apply (subst (1 2) F.map_comp; (rule supp_id_bound bij_id prems)?)
      apply (unfold o_id id_o)
      apply (rule conjI)
      apply ((rule conjI)?,
        (subst F.set_map; (rule supp_id_bound bij_id)?),
        subst image_id,
        rule subprems)+
      apply (rule conjI)
       apply (subst subprems)
       apply (rule Rep_F'_inverse[unfolded mem_Collect_eq])

      apply (subst (2) Rep_F'_inverse[symmetric])
      apply (subst subprems(2)[symmetric])
      apply (rule F.map_cong[THEN arg_cong]; (rule prems refl)?)
      apply (drule rev_subsetD[THEN Collect_case_prodD])
       apply (rule subprems)
      apply (rule sym)
      apply (subst o_apply)
      apply (assumption)
      done
    apply (erule exE)
    apply (erule conjE)
    apply (erule conjE)
    apply (hypsubst_thin)
    subgoal premises subprems for z
      apply (rule exI)
      apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
       apply (rule nonrep2_mapF_bij_2; (rule supp_id_bound bij_id Rep_F'[unfolded mem_Collect_eq])?)
      apply (rule conjI; (rule conjI)?)

        prefer 3(* subgoal 3 is solvable without the exI instantiation and it "instantiates" ?z 
          so that the other 2 subgoals are solvable as well*)
        apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
         apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
        apply (subst F.map_comp; (rule bij_id supp_id_bound prems)?) (*having the id prems before the actual prems is important!*)
        apply (unfold o_id)
        apply (unfold o_def)
        apply (rule F.map_cong; (rule prems refl)?)
        apply (rule snd_conv)

       apply (rule CollectI)
       apply (subst F.set_map; (rule bij_id supp_id_bound)?)+
       apply (unfold image_ident)
       apply (rule conjI; (rule subprems)?)+
        apply (rule subsetI)
        apply (erule imageE)
        apply (rule CollectI)
       apply (rule case_prodI2)
        apply (drule trans[OF sym, THEN iffD1[OF prod.inject]])
         apply (assumption)
        apply (erule conjE)
        apply (rule trans[OF sym])
         apply (assumption)
        apply (erule arg_cong)

      apply (subst F.map_comp; (rule supp_id_bound bij_id)?)
      apply (unfold o_def fst_conv id_def)
      apply (rule refl)
      done
    done
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_strong_tac rrel_F'_def mr_rel_F_def F_strong F_map_id ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
    let
      val _ = prems |> map @{print tracing}
    in
      unfold_thms_tac ctxt [rrel_F'_def] THEN
      HEADGOAL (rtac ctxt (unfold_thms ctxt @{thms inf.idem} 
        (unfold_thms ctxt [mr_rel_F_def, F_map_id] F_strong
         OF (map (fn prem => unfold_thms ctxt [rrel_F'_def] prem) prems))))
    end) ctxt)
\<close>

lemma F'_strong:
  assumes "rrel_F' R x x'" 
    and "rrel_F' Q x x'"
  shows "rrel_F' (inf R Q) x x'" 
  using assms apply -
  apply (tactic \<open>mk_strong_tac @{thm rrel_F'_def} @{thm mr_rel_F_def} @{thm F_strong} @{thm F.map_id} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold rrel_F'_def)
    apply (rule F_strong[unfolded mr_rel_F_def F.map_id, 
          OF prems(1)[unfolded rrel_F'_def] prems(2)[unfolded rrel_F'_def], 
          unfolded inf.idem])
    done
  done

mrbnf "('a::var, 'b::var, 'c::var, 'd) F'"
  map: map_F'
  sets: free: set1_F' bound: set2_F' bound: set3_F' live: set4_F'
  bd: natLeq
  rel: rrel_F'
  var_class: var

  subgoal by (rule F'_map_id)
  subgoal premises prems by (rule F'_map_comp1_; (rule prems))
  subgoal premises prems 
    apply (rule F'_map_cong_; (rule prems ballI)?)
    by (rule prems, assumption)+
  subgoal premises prems 
    apply (rule ext)
    apply (unfold o_apply)
    by(rule F'_set1_map_[OF prems])
  subgoal premises prems
    apply (rule ext)
    apply (unfold o_apply F'_set2_map_[OF prems]) 
    by(rule refl)
  subgoal premises prems 
    apply (rule ext)
    apply (unfold o_apply F'_set3_map_[OF prems]) 
    by(rule refl)
  subgoal premises prems 
    apply (rule ext)
    apply (unfold o_apply F'_set4_map_[OF prems]) 
    by(rule refl)
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by (rule F'_set1_bd)
  subgoal by (rule F'_set2_bd)
  subgoal by (rule F'_set3_bd)
  subgoal by (rule F'_set4_bd)
  subgoal by (rule F'_rel_comp_leq_)
  subgoal premises prems by (rule F'_in_rel[OF prems])
  done        

end