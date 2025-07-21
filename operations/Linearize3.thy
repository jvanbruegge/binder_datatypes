theory Linearize3
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_Recursor"
begin

typedecl ('a, 'b, 'c, 'd, 'e, 'f) F
consts map_F :: "('a \<Rightarrow> 'a') \<Rightarrow> ('b :: var \<Rightarrow> 'b) \<Rightarrow>
  ('c  \<Rightarrow> 'c') \<Rightarrow> ('e \<Rightarrow> 'e') \<Rightarrow> ('f :: var \<Rightarrow> 'f) \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) F \<Rightarrow> ('a', 'b, 'c', 'd, 'e', 'f) F"
consts set1_F :: "('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F \<Rightarrow> 'a set"
consts set2_F :: "('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F \<Rightarrow> 'b set"
consts set3_F :: "('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F \<Rightarrow> 'c set"
consts set5_F :: "('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F \<Rightarrow> 'e set"
consts set6_F :: "('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F \<Rightarrow> 'f set"
consts rrel_F :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'e' \<Rightarrow> bool) \<Rightarrow> ('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F  \<Rightarrow> ('a', 'b, 'c', 'd, 'e', 'f) F \<Rightarrow> bool"


declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
mrbnf "('a, 'b :: var, 'c :: var, 'd, 'e :: var, 'f) F"
  map: map_F
  sets: live: set1_F free: set2_F live: set3_F live: set5_F bound: set6_F
  bd: natLeq
  rel: rrel_F
  var_class: var
  sorry

(* we linearize this MRBNF on position 1*)
ML \<open>val lin_pos = 3\<close>

axiomatization where
  (* The next property assumes preservation of pullbacks on the third position. 
   NB: All MRBNFs already preserve _weak_ pullbacks, i.e., they satisfy the following property 
   without uniqueness.  *)
  F_rel_map_set2_strong: 
  "\<And> R S T (x :: ('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F) y.
    rrel_F R S T x y =
      (\<exists>!z. set1_F z \<subseteq> {(x, y). R x y} \<and>
            set3_F z \<subseteq> {(x, y). S x y} \<and> set5_F z \<subseteq> {(x, y). T x y} \<and> 
            map_F fst id fst fst id z = x \<and> map_F snd id snd snd id z = y)"
  and
  (* The next property assumes that nonrepetitive elements exist: *)
  ex_nonrep: "\<exists>x. \<forall>x'. (\<exists> R. rrel_F (=) R (=) x x') \<longrightarrow> (\<exists> f. x' = map_F id id f id id x)"

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

lemma F_strong:
  "rel_F R1 id R3 R5 id x y \<Longrightarrow> rel_F Q1 id Q3 Q5 id x y \<Longrightarrow> rel_F (inf R1 Q1) id (inf R3 Q3) (inf R5 Q5) id x y"
  by (tactic \<open>mk_F_strong_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm F.map_id} @{thm mr_rel_F_def} @{thm F.mr_rel_mono_strong0}
    @{thm F_rel_map_set2_strong} @{thm F.in_rel} @{context} 
    THEN print_tac @{context} "done"\<close>)


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

(* Another important consequence: the following "exchange"-property, which could be read: 
Since the atoms have a fixed position, we can permute the relations: *)
lemma rel_F_exchange: 
  fixes x :: "('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F" and x' :: "('a', 'b, 'c', 'd, 'e', 'f) F"
  assumes "rel_F R1 id R3 R5 id x x'" and "rel_F Q1 id Q3 Q5 id x x'"
  shows "rel_F Q1 id R3 Q5 id x x'" 
  using assms apply -
  by (tactic \<open>mk_rel_F_exchange_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) 
    @{thm F.mr_rel_mono_strong0} @{thm F_strong} @{context} 
    THEN print_tac @{context} "done"\<close>)

(* Then notion of two items having the same shape (w.r.t. the 1st position): *)
(* these definitions are lin_pos dependent *)
definition sameShape1 :: "('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F \<Rightarrow> ('a,'b,'c,'d,'e,'f) F \<Rightarrow> bool" where 
  "sameShape1 x x' \<equiv> \<exists> R. rel_F (=) id R (=) id x x'"

definition nonrep2 :: "('a, 'b :: var, 'c , 'd, 'e, 'f :: var) F \<Rightarrow> bool" where 
  "nonrep2 x \<equiv> \<forall> x'. sameShape1 x x' \<longrightarrow> (\<exists> f. x' = map_F id id f id id x)"


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
  fixes x :: "('a1, 'a2 :: var, 'a3 , 'a4, 'a5, 'a6 :: var) F"
    and v2 :: "'a2 \<Rightarrow> 'a2" and u6 :: "'a6 \<Rightarrow> 'a6" and g1 :: "'a1 \<Rightarrow> 'b1" and g5 :: "'a5 \<Rightarrow> 'b5"
  assumes "|supp v2| <o |UNIV :: 'a2 set|"
    and "bij u6" "|supp u6| <o |UNIV :: 'a6 set|" 
  assumes "nonrep2 x"
  shows "nonrep2 (map_F g1 v2 id g5 u6 x)"
  using assms apply -
  by (tactic \<open>mk_nonrep2_map_F_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm nonrep2_def} 
    @{thm sameShape1_def} @{thm F.map_comp}  @{thm F.mr_rel_map(1)} @{thm mr_rel_F_def} @{thm F.rel_compp} 
    @{thm F.rel_Grp} @{thm F.map_id} @{thm F.in_rel} @{thms F.rel_map} @{thm F.rel_refl_strong}
    @{context} THEN print_tac @{context} "done"\<close>)

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
  fixes x :: "('a1,'a2::var,'a3,'a4,'a5,'a6::var) F" and u6 :: "'a6\<Rightarrow>'a6" and f :: "'a1 \<Rightarrow> 'a1'" and g :: "'a5 \<Rightarrow> 'a5'"
  assumes "bij u6" "|supp u6| <o |UNIV :: 'a6 set|" 
  assumes "nonrep2 (map_F f id id g u6 x)"
  shows "nonrep2 x"
  using assms apply -
  by (tactic \<open>mk_nonrep2_map_F_rev_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm nonrep2_def} @{thm sameShape1_def} @{thm F.mr_rel_map(1)}
    @{thm F.mr_rel_map(2)} @{thm F.mr_rel_map(3)} @{thm F.map_comp} @{thm F.rel_eq} @{thm F.mr_rel_id} @{thm rel_F_exchange} 
    @{thm F.mr_rel_flip} @{thm F.mr_rel_mono_strong0} @{thm F.mr_rel_Grp} @{context} 
    THEN print_tac @{context} "done"\<close>)


ML\<open>
open BNF_Util BNF_Tactics
fun mk_nonrep2_map_bij_tac mrbnf nonrep_def sameShape_def F_mr_rel_map1 F_mr_rel_map3 F_map_id F_map_comp ctxt = 
  HEADGOAL (Subgoal.FOCUS 
    (fn {prems, context = ctxt, ...} => 
      let
        val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
        val id_prems_v = MRBNF_Comp_Tactics.mk_prems mrbnf @{thms bij_id supp_id_bound} @{thms bij_id supp_id_bound}
        val var_types = var_types_of_mrbnf mrbnf;
        val nr_lives = length (filter (fn v => v = MRBNF_Def.Live_Var) var_types);
        val lin_live_pos = fold_index (fn (i, v) => fn b => 
          if (v = MRBNF_Def.Live_Var andalso i+1 < lin_pos) then b+1 else b) var_types 1;
        val o_id_poses = map_range (fn i => if i < lin_pos-1 then i*2 + 7 else (i+1)*2 + 7) (length var_types-1) |> filter (fn n => n >= 0);
      in
        unfold_thms_tac ctxt [nonrep_def, sameShape_def] THEN
        HEADGOAL (EVERY' [
          rtac ctxt allI,
          rtac ctxt impI,
          etac ctxt exE,
          dtac ctxt (rotate_prems ~1 (F_mr_rel_map1 RS iffD1)) THEN_ALL_NEW
            TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
          K (unfold_thms_tac ctxt @{thms o_id Grp_UNIV_id}),
          EqSubst.eqsubst_asm_tac ctxt [lin_live_pos*3 - 1] [@{thm OO_eq} RS sym],
          EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_lives*2 -1)) [@{thm conversep_eq} RS sym],
          EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_lives*2 -1)) @{thms eq_alt},
          EqSubst.eqsubst_asm_tac ctxt [1] [@{thm inv_o_simp2} OF [(nth prems 0)] RS sym],
          K (unfold_thms_tac ctxt @{thms Grp_o converse_relcompp}),
          EqSubst.eqsubst_asm_tac ctxt [1] [@{thm relcompp_assoc} RS sym],
          dtac ctxt ((unfold_thms ctxt @{thms inv_id o_id} (F_mr_rel_map3 OF 
            (id_prems @ id_prems_v) RS sym)) RS iffD1),
          K (unfold_thms_tac ctxt @{thms Grp_UNIV_id conversep_eq}),
          dtac ctxt (Object_Logic.rulify ctxt (unfold_thms ctxt [nonrep_def, sameShape_def] (nth prems 1)) OF [exI]),
          etac ctxt exE
        ]) THEN
        HEADGOAL (Subgoal.FOCUS 
          (fn {prems = subprems, context = ctxt, ...} => 
            HEADGOAL (EVERY' [
              EqSubst.eqsubst_tac ctxt [0] [F_map_id RS sym],
              EqSubst.eqsubst_tac ctxt o_id_poses [@{thm o_id} RS sym],
              EqSubst.eqsubst_tac ctxt [1] [@{thm inv_o_simp2} OF [(nth prems 0)] RS sym],
              K (unfold_thms_tac ctxt [F_map_comp OF flat (replicate 2 id_prems) RS sym]),
              EqSubst.eqsubst_tac ctxt [1] subprems,
              EqSubst.eqsubst_tac ctxt [2*lin_pos + 6 + 2*(length var_types)] [@{thm o_id} RS sym],
              EqSubst.eqsubst_tac ctxt [1] [@{thm inv_o_simp1} OF [(nth prems 0)] RS sym],
              K (unfold_thms_tac ctxt [F_map_comp OF flat (replicate 2 id_prems)]),
              EqSubst.eqsubst_tac ctxt [1, 2] @{thms o_assoc},
              rtac ctxt exI,
              rtac ctxt refl
            ])
          ) ctxt)
      end)
  ctxt)
\<close>

lemma nonrep2_mapF_bij:
  fixes x :: "('a1,'a2::var,'a3,'a4,'a5,'a6::var) F" and g::"'a3\<Rightarrow>'a3"
  assumes g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F id id g id id x)" (is "nonrep2 ?x'")
  using assms apply -
  by (tactic \<open>mk_nonrep2_map_bij_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm nonrep2_def}
    @{thm sameShape1_def} @{thm F.mr_rel_map(1)} @{thm F.mr_rel_map(3)} @{thm F.map_id} @{thm F.map_comp} @{context}
    THEN print_tac @{context} "done"\<close>)


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
  fixes x :: "('a1,'a2::var,'a3,'a4,'a5,'a6::var) F"
    and f :: "'a1 \<Rightarrow> 'a1'" and v2 :: "'a2\<Rightarrow>'a2" and g::"'a3\<Rightarrow>'a3" and h::"'a5\<Rightarrow>'a5'" and u6::"'a6\<Rightarrow>'a6"
  assumes v2: "|supp v2| <o |UNIV :: 'a2 set|" 
    and u6: "bij u6" "|supp u6| <o |UNIV :: 'a6 set|"
    and g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F f v2 g h u6 x)" 
  using assms apply -
  by (tactic \<open>mk_nonrep2_mapF_bij_2_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) 
    @{thm nonrep2_mapF_bij} @{thm nonrep2_map_F} @{thm F.map_comp} @{context} 
    THEN print_tac @{context} "done"\<close>)


typedef ('a1,'a2::var,'a3,'a4,'a5,'a6::var) F' = "{x :: ('a1,'a2,'a3,'a4,'a5,'a6) F. nonrep2 x}"
  apply (unfold mem_Collect_eq nonrep2_def sameShape1_def mr_rel_F_def F.map_id)
  by (rule ex_nonrep)

definition set1_F' :: "('a1,'a2::var,'a3,'a4,'a5,'a6::var) F' \<Rightarrow> 'a1 set" where "set1_F' = set1_F o Rep_F'"
definition set2_F' :: "('a1,'a2::var,'a3,'a4,'a5,'a6::var) F' \<Rightarrow> 'a2 set" where "set2_F' = set2_F o Rep_F'"
definition set3_F' :: "('a1,'a2::var,'a3,'a4,'a5,'a6::var) F' \<Rightarrow> 'a3 set" where "set3_F' = set3_F o Rep_F'"
definition set5_F' :: "('a1,'a2::var,'a3,'a4,'a5,'a6::var) F' \<Rightarrow> 'a5 set" where "set5_F' = set5_F o Rep_F'"
definition set6_F' :: "('a1,'a2::var,'a3,'a4,'a5,'a6::var) F' \<Rightarrow> 'a6 set" where "set6_F' = set6_F o Rep_F'"

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV :: 'a set| then f else id"

definition map_F' :: "('a1 \<Rightarrow> 'a1') \<Rightarrow> ('a2::var \<Rightarrow> 'a2) \<Rightarrow> ('a3::var \<Rightarrow> 'a3) \<Rightarrow> ('a5 \<Rightarrow> 'a5') \<Rightarrow> ('a6::var \<Rightarrow> 'a6)
  \<Rightarrow> ('a1,'a2,'a3,'a4,'a5,'a6) F' \<Rightarrow> ('a1','a2,'a3,'a4,'a5','a6) F'"
  where "map_F' f v2 g h u6 = Abs_F' o map_F f (asSS v2) (asBij g) h (asSS (asBij u6)) o Rep_F'"

definition rrel_F' :: "('a1 \<Rightarrow> 'a1' \<Rightarrow> bool) \<Rightarrow> ('a5 \<Rightarrow> 'a5' \<Rightarrow> bool) \<Rightarrow> ('a1,'a2::var,'a3,'a4,'a5,'a6::var) F' \<Rightarrow> ('a1','a2,'a3,'a4,'a5','a6) F' \<Rightarrow> bool"
  where "rrel_F' R Q x x' = rrel_F R (=) Q (Rep_F' x) (Rep_F' x')"

(* Verifying the axioms of a MRBNF for F':  *)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_map_id_tac map_F'_def F_map_id Rep_F'_inverse ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {context = ctxt, ...} =>
      unfold_thms_tac ctxt ([map_F'_def, 
        eqTrueI OF @{thms bij_id}, eqTrueI OF @{thms supp_id_bound}] @ 
        @{thms asSS_def asBij_def if_True}) THEN
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [F_map_id, Rep_F'_inverse, @{thm o_apply}] THEN
      unfold_thms_tac ctxt @{thms id_def} THEN
      HEADGOAL (rtac ctxt refl)
     ) ctxt)
\<close>

lemma F'_map_id: "map_F' id id id id id = id"
  by (tactic \<open>mk_map_id_tac @{thm map_F'_def} @{thm F.map_id} @{thm Rep_F'_inverse} @{context} 
    THEN print_tac @{context} "done"\<close>)


ML \<open>
open BNF_Util BNF_Tactics

fun mk_map_comp_tac mrbnf map_F'_def Abs_F'_inverse Rep_F' nonrep2_mapF_bij_2 F_map_comp0 ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems, context = ctxt, ...} =>
    let
      val var_types = var_types_of_mrbnf mrbnf;
      val nr_bounds = length (filter (fn v => v = MRBNF_Def.Bound_Var) var_types);
      val nr_frees = length (filter (fn v => v = MRBNF_Def.Free_Var) var_types);
    in
      unfold_thms_tac ctxt (map_F'_def:: @{thms asSS_def asBij_def}) THEN
      HEADGOAL(EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (1 + 2*nr_bounds)) @{thms bij_comp} THEN_ALL_NEW
        TRY o resolve_tac ctxt prems) THEN
      unfold_thms_tac ctxt @{thms if_True} THEN
      HEADGOAL (EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (nr_bounds + nr_frees)) @{thms supp_comp_bound} THEN_ALL_NEW
        TRY o resolve_tac ctxt (@{thm infinite_UNIV} ::prems)) THEN
      unfold_thms_tac ctxt (@{thm if_True} :: map (fn thm => thm RS eqTrueI) prems) THEN
      HEADGOAL (rtac ctxt ext) THEN
      HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [F_map_comp0] THEN_ALL_NEW
        TRY o resolve_tac ctxt prems) THEN
      unfold_thms_tac ctxt [o_apply] THEN
      HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
        rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems),
        rtac ctxt refl])
    end) ctxt)
\<close>


lemma F'_map_comp1_:
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u6 v6 :: "'a6::var \<Rightarrow> 'a6"
  assumes "|supp u2| <o |UNIV :: 'a2 set|" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  assumes "bij u6" "|supp u6| <o |UNIV :: 'a6 set|" "bij v6" "|supp v6| <o |UNIV :: 'a6 set|"
  shows "map_F' (f' o f) (v2 o u2) (v3 o u3) (g' o g) (v6 o u6) = map_F' f' v2 v3 g' v6 o map_F' f u2 u3 g u6"
  using assms apply -
  by (tactic \<open>mk_map_comp_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.map_comp0} @{context} 
    THEN print_tac @{context} "done"\<close>)


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
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u6 :: "'a6::var \<Rightarrow> 'a6"
  assumes "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u6" "|supp u6| <o |UNIV :: 'a6 set|"
  shows "set1_F' (map_F' f u2 u3 g u6 b) = f ` set1_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set1_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(1)} @{context} 
    THEN print_tac @{context} "done"\<close>)

lemma F'_set2_map_:
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u6 :: "'a6::var \<Rightarrow> 'a6"
  assumes "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u6" "|supp u6| <o |UNIV :: 'a6 set|"
  shows "set2_F' (map_F' f u2 u3 g u6 b) = u2 ` set2_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set2_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(2)} @{context}\<close>)

lemma F'_set3_map_:
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u6 :: "'a6::var \<Rightarrow> 'a6"
  assumes "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u6" "|supp u6| <o |UNIV :: 'a6 set|"
  shows "set3_F' (map_F' f u2 u3 g u6 b) = u3 ` set3_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set3_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(3)} @{context}\<close>)

lemma F'_set5_map_:
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u6 :: "'a6::var \<Rightarrow> 'a6"
  assumes "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u6" "|supp u6| <o |UNIV :: 'a6 set|"
  shows "set5_F' (map_F' f u2 u3 g u6 b) = g ` set5_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set5_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(4)} @{context}\<close>)

lemma F'_set6_map_:
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u6 :: "'a6::var \<Rightarrow> 'a6"
  assumes "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u6" "|supp u6| <o |UNIV :: 'a6 set|"
  shows "set6_F' (map_F' f u2 u3 g u6 b) = u6 ` set6_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set6_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(5)} @{context}\<close>)


ML \<open>
open BNF_Util BNF_Tactics

fun mk_map_cong_tac map_F'_def F_map_cong set_F'_defs ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} =>
      unfold_thms_tac ctxt ([map_F'_def] @ map (fn thm => thm RS eqTrueI) prems @
        @{thms asSS_def asBij_def if_True o_apply}) THEN
      HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [F_map_cong] THEN_ALL_NEW
        TRY o resolve_tac ctxt (rev prems)) THEN
      HEADGOAL (rtac ctxt refl) THEN
      REPEAT_DETERM_N (length set_F'_defs) (HEADGOAL (
        eresolve_tac ctxt (map_index (fn (i, def) => bspec OF [unfold_thms ctxt [def, @{thm o_apply}] 
          (nth prems (length prems - 1 - i))]) (rev set_F'_defs)))) THEN
      HEADGOAL (rtac ctxt refl)
    ) ctxt)
\<close>

lemma F'_map_cong_[fundef_cong]:
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u6 v6 :: "'a6::var \<Rightarrow> 'a6"
  assumes "|supp u2| <o |UNIV :: 'a2 set|" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  assumes "bij u6" "|supp u6| <o |UNIV :: 'a6 set|" "bij v6" "|supp v6| <o |UNIV :: 'a6 set|"
    and "\<forall> a \<in> set1_F' x. f a = f' a"
    and "\<forall> a \<in> set2_F' x. u2 a = v2 a"
    and "\<forall> a \<in> set3_F' x. u3 a = v3 a"
    and "\<forall> a \<in> set5_F' x. g a = g' a"
    and "\<forall> a \<in> set6_F' x. u6 a = v6 a"
  shows "map_F' f u2 u3 g u6 x = map_F' f' v2 v3 g' v6 x"
  using assms apply -
  by (tactic \<open>mk_map_cong_tac @{thm map_F'_def} @{thm F.map_cong} 
    @{thms set1_F'_def set2_F'_def set3_F'_def set5_F'_def set6_F'_def} @{context} 
    THEN print_tac @{context} "done"\<close>)

(* This tactic is applicable to all 4 of the following <F'_setx_bd> lemmas*)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_set_bd_tac set_F'_def F_set_bd ctxt =
    unfold_thms_tac ctxt [set_F'_def, o_apply] THEN
    HEADGOAL (rtac ctxt F_set_bd)
\<close>

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set1_F'_def} @{thm F.set_bd(1)} @{context}\<close>)
lemma F'_set2_bd: "\<And>b. |set2_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set2_F'_def} @{thm F.set_bd(2)} @{context}\<close>)
lemma F'_set3_bd: "\<And>b. |set3_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set3_F'_def} @{thm F.set_bd(3)} @{context}\<close>)
lemma F'_set5_bd: "\<And>b. |set5_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set5_F'_def} @{thm F.set_bd(4)} @{context}\<close>)
lemma F'_set6_bd: "\<And>b. |set6_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set6_F'_def} @{thm F.set_bd(5)} @{context}\<close>)

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rel_comp_leq_tac mrbnf rrel_F'_def F_rel_compp ctxt =
  let
    val var_types = var_types_of_mrbnf mrbnf;
    val lin_live_pos = fold_index (fn (i, v) => fn b => 
      if (v = MRBNF_Def.Live_Var andalso i+1 < lin_pos) then b+1 else b) var_types 1;
  in
    HEADGOAL (EVERY' [
      rtac ctxt @{thm predicate2I},
      etac ctxt @{thm relcomppE},
      K (unfold_thms_tac ctxt [rrel_F'_def]),
      EqSubst.eqsubst_tac ctxt [5] (@{thms eq_OO[symmetric]}),
      K (print_tac ctxt "no?"),
      EqSubst.eqsubst_tac ctxt [1] ([F_rel_compp]),
      K (unfold_thms_tac ctxt [rrel_F'_def]),
      rtac ctxt @{thm relcomppI} THEN_ALL_NEW assume_tac ctxt
    ])
  end
\<close>

lemma F'_rel_comp_leq_: "rrel_F' Q Q' OO rrel_F' R R' \<le> rrel_F' (Q OO R) (Q' OO R')"
  by (tactic \<open>mk_rel_comp_leq_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm rrel_F'_def} @{thm F.rel_compp} @{context}
    THEN print_tac @{context} "done"\<close>)

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rrel_F_map_F3_tac F_rel_map F_rel_mono_strong Grp_def ctxt =
    unfold_thms_tac ctxt ([F_rel_map, Grp_def, eqTrueI OF @{thms UNIV_I}] @ @{thms id_apply simp_thms(21)}) THEN
    HEADGOAL (rtac ctxt @{thm iffI}) THEN
    ALLGOALS (etac ctxt F_rel_mono_strong THEN_ALL_NEW
       (assume_tac ctxt ORELSE' etac ctxt sym))
\<close>

lemma rrel_F_map_F3:
  fixes x :: "('a,'b::var,'c,'d,'e,'f::var) F"
  shows "rrel_F R (Grp (f :: 'c \<Rightarrow> 'c)) Q x y = rrel_F R (=) Q (map_F id id f id id x) y"
  by (tactic \<open>mk_rrel_F_map_F3_tac @{thm F.rel_map(1)} @{thm F.rel_mono_strong} @{thm Grp_def} @{context} 
    THEN print_tac @{context} "done"\<close>)

ML \<open>
open BNF_Util BNF_Tactics

fun mk_asSS_tac ctxt =
  unfold_thms_tac ctxt @{thms asSS_def} THEN
  HEADGOAL (rtac ctxt @{thm if_P}) THEN
  HEADGOAL (assume_tac ctxt)
\<close>

lemma asSS: "|supp u| <o |UNIV :: 'a set| \<Longrightarrow> asSS (u :: 'a \<Rightarrow> 'a) = u"
  by (tactic \<open>mk_asSS_tac @{context} 
    THEN print_tac @{context} "done"\<close>)

ML \<open>
open BNF_Util BNF_Tactics MRBNF_Def

fun mk_in_rel_tac mrbnf rrel_F'_def map_F'_def Abs_F'_inverse Rep_F' nonrep2_mapF_bij_2 
  rrel_F_map_F3 F_in_rel F_map_comp nonrep2_map_F_rev Rep_F'_inverse F_map_cong set_F'_defs F_set_maps cx ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt,...} =>
      let
        val var_types = var_types_of_mrbnf mrbnf;
        val nr_lives = length (filter (fn v => v = Live_Var) var_types);
      in
        unfold_thms_tac ctxt ([rrel_F'_def, map_F'_def, o_apply] @ set_F'_defs @ @{thms asSS_def asBij_def if_True} @ 
          map (fn thm => thm RS eqTrueI) (prems @ @{thms supp_id_bound bij_id})) THEN
        HEADGOAL (EVERY' [
          EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
          rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems),
          EqSubst.eqsubst_tac ctxt (map_range (fn i => 7+2*(i+nr_lives)) (length var_types)) [@{thm id_o} RS sym],
          EqSubst.eqsubst_tac ctxt [lin_pos] [trans OF [@{thm id_o}, @{thm o_id} RS sym]],
          EqSubst.eqsubst_tac ctxt [1] [F_map_comp RS sym] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms bij_id supp_id_bound}),
          EqSubst.eqsubst_tac ctxt [1] [rrel_F_map_F3 RS sym],
          EqSubst.eqsubst_tac ctxt [1] [F_in_rel] THEN_ALL_NEW
            TRY o resolve_tac ctxt prems
        ]) THEN
        unfold_thms_tac ctxt ((eqTrueI OF @{thms UNIV_I}):: @{thms Grp_def simp_thms(21)}) THEN
        HEADGOAL (rtac ctxt iffI) THEN
        (* 1st Subgoal *)
        REPEAT_DETERM_N (3+nr_lives) (HEADGOAL (eresolve_tac ctxt [exE, conjE, CollectE])) THEN
        HEADGOAL (Subgoal.FOCUS
          (fn {prems = subprems, context = ctxt, ...} =>
              (* setup *)
              HEADGOAL (EVERY' [
                rtac ctxt exI,
                EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (nr_lives+1)) [Abs_F'_inverse],
                Method.insert_tac ctxt [unfold_thms ctxt [(nth subprems 0 RS sym)] (infer_instantiate' ctxt [SOME cx] Rep_F')],
                EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => 4+2*i) (length var_types)) [@{thm o_id} RS sym],
                EqSubst.eqsubst_asm_tac ctxt [lin_pos] [trans OF [@{thm o_id}, @{thm id_o} RS sym]],
                EqSubst.eqsubst_asm_tac ctxt [0] [F_map_comp RS sym] THEN_ALL_NEW
                  TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
                dtac ctxt (rotate_prems ~1 nonrep2_map_F_rev) THEN_ALL_NEW
                  TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
                assume_tac ctxt
              ]) THEN
              (* solve *)
              HEADGOAL (EqSubst.eqsubst_tac ctxt [1, 2] [F_map_comp] THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms bij_id supp_id_bound})) THEN
              unfold_thms_tac ctxt @{thms id_o o_id} THEN
              HEADGOAL (rtac ctxt conjI) THEN
              REPEAT_DETERM_N (nr_lives-1) (HEADGOAL (EVERY' [
                TRY o rtac ctxt conjI,
                EqSubst.eqsubst_tac ctxt [0] F_set_maps THEN_ALL_NEW 
                  TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
                EqSubst.eqsubst_tac ctxt [0] @{thms image_id},
                resolve_tac ctxt subprems
              ])) THEN
              HEADGOAL (EVERY' [
                EqSubst.eqsubst_tac ctxt [2, 4] [Rep_F'_inverse RS sym],
                rtac ctxt conjI,
                rtac ctxt (arg_cong OF [nth subprems 0]),
                EqSubst.eqsubst_tac ctxt [0] [nth subprems 1 RS sym],
                rtac ctxt (F_map_cong RS arg_cong) THEN_ALL_NEW
                  TRY o resolve_tac ctxt (refl::prems),
                dtac ctxt (@{thm rev_subsetD} RS @{thm Collect_case_prodD}),
                resolve_tac ctxt subprems,
                rtac ctxt sym,
                EqSubst.eqsubst_tac ctxt [0] [o_apply],
                assume_tac ctxt
              ])
            ) 
          ctxt) THEN
        (* 2nd Subgoal *)
        REPEAT_DETERM_N (1+nr_lives) (HEADGOAL (eresolve_tac ctxt [exE, conjE])) THEN
        HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
        HEADGOAL (Subgoal.FOCUS
          (fn {prems = subprems, context = ctxt, ...} =>
            HEADGOAL (EVERY' [
              rtac ctxt exI,
              EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
              rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW
                TRY o resolve_tac ctxt (Rep_F':: @{thms supp_id_bound bij_id}),
              rtac ctxt conjI THEN_ALL_NEW TRY o rtac ctxt conjI 
            ]) THEN
            prefer_tac 3 THEN
            HEADGOAL (EVERY' [
              EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
              rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW                
                TRY o resolve_tac ctxt (Rep_F':: prems),
              EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                TRY o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems),
              K (unfold_thms_tac ctxt @{thms o_id}),
              K (unfold_thms_tac ctxt @{thms o_def}),
              rtac ctxt F_map_cong THEN_ALL_NEW
                TRY o resolve_tac ctxt (refl::prems),
              rtac ctxt @{thm snd_conv},
              rtac ctxt CollectI
            ]) THEN
            REPEAT_DETERM_N (nr_lives) (
              HEADGOAL (EqSubst.eqsubst_tac ctxt [0] F_set_maps THEN_ALL_NEW
                TRY o resolve_tac ctxt @{thms bij_id supp_id_bound})) THEN
            unfold_thms_tac ctxt @{thms image_ident} THEN
            REPEAT_DETERM_N (nr_lives-1) (
              HEADGOAL (rtac ctxt conjI THEN_ALL_NEW
                TRY o resolve_tac ctxt subprems)) THEN
            HEADGOAL (EVERY' [
              rtac ctxt subsetI,
              etac ctxt imageE,
              rtac ctxt CollectI,
              rtac ctxt @{thm case_prodI2},
              dtac ctxt (trans OF [sym] RS (iffD1 OF @{thms prod.inject})),
              assume_tac ctxt,
              etac ctxt conjE,
              rtac ctxt (trans OF [sym]),
              assume_tac ctxt,
              etac ctxt arg_cong,
              EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                TRY o resolve_tac ctxt @{thms supp_id_bound bij_id},
              K (unfold_thms_tac ctxt @{thms o_def id_def fst_conv}),
              rtac ctxt refl
            ])) 
          ctxt) 
    end) ctxt)
\<close>


lemma F'_in_rel:
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u6 :: "'a6::var \<Rightarrow> 'a6"
  assumes u2: "|supp u2| <o |UNIV :: 'a2 set|" 
    and u3: "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
    and u6: "bij u6" "|supp u6| <o |UNIV :: 'a6 set|"
  shows "rrel_F' R Q (map_F' id u2 u3 id u6 x) y =
    (\<exists>z. (set1_F' z \<subseteq> {(x, y). R x y} \<and> set5_F' z \<subseteq> {(x, y). Q x y}) \<and> map_F' fst id id fst id z = x \<and> map_F' snd u2 u3 snd u6 z = y)"
  using assms apply -
  by (tactic \<open>mk_in_rel_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm rrel_F'_def} 
    @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm rrel_F_map_F3} @{thm F.in_rel}
    @{thm F.map_comp} @{thm nonrep2_map_F_rev} @{thm Rep_F'_inverse} @{thm F.map_cong} 
    @{thms set1_F'_def set5_F'_def} @{thms F.set_map}
    @{cterm x} @{context}
    THEN print_tac @{context} "done"\<close>)

ML \<open>
open BNF_Util BNF_Tactics

fun mk_strong_tac rrel_F'_def mr_rel_F_def F_strong F_map_id ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      unfold_thms_tac ctxt [rrel_F'_def] THEN
      HEADGOAL (rtac ctxt (unfold_thms ctxt @{thms inf.idem} 
        (unfold_thms ctxt [mr_rel_F_def, F_map_id] F_strong
         OF (map (fn prem => unfold_thms ctxt [rrel_F'_def] prem) prems))))
    ) ctxt)
\<close>

lemma F'_strong:
  assumes "rrel_F' R Q x x'" 
    and "rrel_F' R' Q' x x'"
  shows "rrel_F' (inf R R') (inf Q Q') x x'" 
  using assms apply -
  by (tactic \<open>mk_strong_tac @{thm rrel_F'_def} @{thm mr_rel_F_def} @{thm F_strong} @{thm F.map_id} @{context} 
    THEN print_tac @{context} "done"\<close>)


mrbnf "('a :: var, 'b :: var, 'c :: var, 'd, 'e , 'f:: var) F'"
  map: map_F'
  sets: live: set1_F' free: set2_F' bound: set3_F' live: set5_F' bound: set6_F'
  bd: natLeq
  rel: rrel_F'
  var_class: var
  subgoal by (rule F'_map_id)
  subgoal premises prems by (rule F'_map_comp1_; (rule prems))
  subgoal premises prems 
    apply (rule F'_map_cong_; (rule prems ballI))
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
    apply (unfold o_apply F'_set5_map_[OF prems]) 
    by(rule refl)
  subgoal premises prems 
    apply (rule ext)
    apply (unfold o_apply F'_set6_map_[OF prems]) 
    by(rule refl)
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by (rule F'_set1_bd)
  subgoal by (rule F'_set2_bd)
  subgoal by (rule F'_set3_bd)
  subgoal by (rule F'_set5_bd)
  subgoal by (rule F'_set6_bd)
  subgoal by (rule F'_rel_comp_leq_)
  subgoal premises prems by (rule F'_in_rel; rule prems)
  done        

end