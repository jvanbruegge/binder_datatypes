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
  ex_nonrep: "\<exists>x. \<forall>x'. (\<exists> R. rrel_F R (=) x x') \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

abbreviation "rel_F \<equiv> mr_rel_F"


(* necessary helper for F_strong *)
ML \<open>
open BNF_Util BNF_Tactics
fun mk_inf_apply_2_set_tac ctxt =
  HEADGOAL (EVERY' [
    rtac ctxt @{thm Collect_cong},
    rtac ctxt @{thm prod.case_cong},
    rtac ctxt refl,
    K (unfold_thms_tac ctxt [@{thm inf_apply}]),
    rtac ctxt refl
  ])
\<close>
lemma inf_apply_2_set: "{(x, y). inf A B x y} = {(x, y). inf (A x y) (B x y)}"
  by (tactic \<open>mk_inf_apply_2_set_tac @{context}\<close>)


(* Important consequence of preservation of pullbacks (which is actually equivalent to it): 
The relator is closed under intersections. *)

ML \<open>
open BNF_Util BNF_Tactics

fun mk_F_strong_tac F_map_id mr_rel_F_def F_mr_rel_mono_strong0 F_rel_map_set2_strong F_in_rel ctxt =
  HEADGOAL (
    forward_tac ctxt [F_mr_rel_mono_strong0 OF @{thms supp_id_bound bij_id supp_id_bound 
      supp_id_bound bij_id supp_id_bound}] THEN_ALL_NEW (
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
    @{thms supp_id_bound bij_id supp_id_bound}), sym OF @{thms id_def}, mem_Collect_eq]) THEN
  HEADGOAL (etac ctxt exE) THEN
  HEADGOAL (etac ctxt exE) THEN
  HEADGOAL (etac ctxt @{thm alt_ex1E}) THEN
  REPEAT_DETERM_N 7 (HEADGOAL (etac ctxt conjE)) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, params, ...} => 
    let
      val _ = prems |> map @{print tracing}
      val _ = params |> map @{print tracing}
    in
      print_tac @{context} "SUBGOAL" THEN
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
      unfold_thms_tac ctxt @{thms inf_apply_2_set inf_bool_def} THEN
      HEADGOAL (rtac ctxt conjI) THEN

      HEADGOAL (Method.insert_tac ctxt prems) THEN
      HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
      HEADGOAL (rtac ctxt conjI) THEN
      REPEAT_DETERM_N 2 (HEADGOAL (EVERY' [
        rtac ctxt @{thm subrelI},
        rtac ctxt CollectI,
        rtac ctxt @{thm case_prodI},
        rtac ctxt conjI THEN_ALL_NEW 
          etac ctxt (@{thm rev_subsetD} RS (iffD1 OF @{thms prod_in_Collect_iff})),
      assume_tac ctxt,
      assume_tac ctxt])) THEN

      HEADGOAL (rtac ctxt conjI THEN_ALL_NEW resolve_tac ctxt prems)
end ) ctxt)
\<close>

lemma F_strong:
  "rel_F id id R3 R4 x y \<Longrightarrow> rel_F id id Q3 Q4 x y \<Longrightarrow> rel_F id id (inf R3 Q3) (inf R4 Q4) x y"
  apply (tactic \<open>mk_F_strong_tac @{thm F.map_id} @{thm mr_rel_F_def} @{thm F.mr_rel_mono_strong0}
    @{thm F_rel_map_set2_strong} @{thm F.in_rel} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)

  apply (frule F.mr_rel_mono_strong0[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound];
      ((rule ballI, rule ballI refl)?, 
        (rule impI, rule trans[OF top_apply[THEN fun_cong] trans[OF top_apply top_bool_def]])?))
  apply(rotate_tac 2)
  apply (unfold F.map_id mr_rel_F_def eq_True)
  apply (drule F_rel_map_set2_strong[THEN iffD1])
  apply (unfold top_apply top_bool_def Collect_const_case_prod if_True eqTrueI[OF subset_UNIV] simp_thms(22))
  apply (unfold F.in_rel[OF supp_id_bound bij_id supp_id_bound, unfolded id_apply F.map_id OO_Grp_alt]
      id_def[symmetric] mem_Collect_eq)
  apply (elim exE alt_ex1E)
  apply (erule conjE)+
  subgoal premises subprems for z l r
    apply (insert spec2[OF subprems(1), of r z]
        spec2[OF subprems(1), of l z]; (erule impE); (erule impE))
       apply (rule conjI; rule conjI; rule subprems)+
    apply (rule exI)
    apply (unfold inf_apply_2_set inf_bool_def)
    apply (rule conjI)
     apply (insert subprems) []
     apply (hypsubst_thin)
     apply (rule conjI)
      apply (rule subrelI, 
        rule CollectI, 
        rule case_prodI, 
        (rule conjI; erule rev_subsetD[THEN iffD1[OF prod_in_Collect_iff]]),
        assumption, assumption)+
    apply (rule conjI)
    apply(rule subprems)+
    done
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rel_F_exchange_tac F_mr_rel_mono_strong0 F_strong ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt (F_mr_rel_mono_strong0 
          OF @{thms supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound})) THEN
      HEADGOAL (rtac ctxt (F_strong OF prems)) THEN
      unfold_thms_tac ctxt ([id_apply, eqTrueI OF [refl]] @ @{thms ball_triv inf_apply inf_bool_def}) THEN
      ALLGOALS (TRY o (rtac ctxt ballI THEN_ALL_NEW rtac ctxt ballI) 
        THEN_ALL_NEW rtac ctxt impI) THEN
      HEADGOAL (rtac ctxt TrueI) THEN
      HEADGOAL (rtac ctxt TrueI) THEN
      HEADGOAL (etac ctxt conjunct1) THEN
      HEADGOAL (etac ctxt conjunct2)
     ) ctxt)
\<close>

(* Another important consequence: the following "exchange"-property, which could be read: 
Since the atoms have a fixed position, we can permute the relations: *)
lemma rel_F_exchange: 
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and x' :: "('a1,'a2,'a3','a4') F"
  assumes "rel_F id id R2 R3 x x'" and "rel_F id id Q2 Q3 x x'"
  shows "rel_F id id R2 Q3 x x'" 
  using assms apply -
  apply (tactic \<open>mk_rel_F_exchange_tac @{thm F.mr_rel_mono_strong0} @{thm F_strong} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (rule F.mr_rel_mono_strong0[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound])
    apply (rule F_strong[OF prems])
       apply (unfold id_apply eqTrueI[OF refl] ball_triv inf_apply inf_bool_def)
       apply (intro impI TrueI)
       apply (intro impI TrueI)
     apply (intro ballI impI)
     apply (erule conjunct1)
    apply (intro ballI impI)
    apply (erule conjunct2)
    done
  done


(* Then notion of two items having the same shape (w.r.t. the 3rd position): *)
definition sameShape1 :: "('a1::var,'a2::var,'a3,'a4) F \<Rightarrow> ('a1,'a2,'a3,'a4) F \<Rightarrow> bool" where 
  "sameShape1 x x' \<equiv> \<exists> R. rel_F id id R (=) x x'"

definition nonrep2 :: "('a1::var,'a2::var,'a3,'a4) F \<Rightarrow> bool" where 
  "nonrep2 x \<equiv> \<forall> x'. sameShape1 x x' \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

(* this is not used anywhere. A ML tactic is not needed then? *)
lemma op_eq_triv_sym: "(\<lambda>x. (=) (g x)) = (\<lambda>x z. z = g x)"
  apply (intro ext)
  apply (rule eq_commute)
  done

ML\<open>
open BNF_Util BNF_Tactics

fun mk_nonrep2_map_F_tac nonrep_def sameShape_def F_map_comp F_mr_rel_map mr_rel_F_def F_rel_compp 
  F_rel_Grp F_map_id F_in_rel F_rel_map1 F_rel_map2 F_rel_refl_strong ctxt = 
  HEADGOAL (Subgoal.FOCUS 
    (fn {prems, context = ctxt, ...} => 
      let
        val unfold_map_comp = F_map_comp OF ((take 3 prems) @ @{thms supp_id_bound bij_id supp_id_bound});
        val fold_map_comp = F_map_comp OF (@{thms supp_id_bound bij_id supp_id_bound} @ (take 3 prems)) RS sym;
        val switch = (fn thm1 => (fn thm2 => trans OF [thm1, thm2 RS sym]));
        val o_id = @{thm o_id};
        val id_o = @{thm id_o};
      in
        unfold_thms_tac ctxt [nonrep_def, sameShape_def] THEN
        HEADGOAL (EVERY' [
          rtac ctxt allI,
          rtac ctxt impI,
          etac ctxt exE,
          EqSubst.eqsubst_tac ctxt [0] [unfold_map_comp],
          EqSubst.eqsubst_tac ctxt [1] [switch o_id id_o],
          EqSubst.eqsubst_tac ctxt [1, 2, 4] [switch id_o o_id],
          EqSubst.eqsubst_tac ctxt [0] [fold_map_comp],
          dtac ctxt (F_mr_rel_map OF ((take 3 prems) @ @{thms supp_id_bound bij_id supp_id_bound}) RS iffD1),
          EqSubst.eqsubst_asm_tac ctxt [1, 2] [switch id_o o_id],
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms Grp_UNIV_id},
          EqSubst.eqsubst_asm_tac ctxt [1] [switch @{thm OO_eq} @{thm eq_OO}],
          EqSubst.eqsubst_asm_tac ctxt [1] [switch @{thm eq_OO} @{thm OO_eq}],
          EqSubst.eqsubst_asm_tac ctxt [1, 2] @{thms eq_alt}          
        ]) THEN
        unfold_thms_tac ctxt [mr_rel_F_def, o_id, F_rel_compp, F_rel_Grp, F_map_id] THEN
        unfold_thms_tac ctxt [eqTrueI OF @{thms subset_UNIV}, @{thm simp_thms(21)}, id_o, @{thm UNIV_def} RS sym] THEN
        unfold_thms_tac ctxt ((eqTrueI OF [@{thm UNIV_I}]):: @{thms Grp_UNIV_id OO_def Grp_def simp_thms(21)}) THEN
        HEADGOAL (EVERY' [
          EqSubst.eqsubst_asm_tac ctxt [1] [id_apply],
          etac ctxt exE,
          etac ctxt conjE,
          dtac ctxt (F_in_rel OF (take 3 prems) RS iffD1),
          Method.insert_tac ctxt [unfold_thms ctxt [nonrep_def, sameShape_def, mr_rel_F_def, F_map_id] (nth prems 3)],
          etac ctxt exE,
          etac ctxt conjE,
          etac ctxt CollectE,
          etac ctxt conjE,
          etac ctxt conjE,
          hyp_subst_tac_thin true ctxt
        ]) THEN
        HEADGOAL (Subgoal.FOCUS 
          (fn {prems = subprems, context = ctxt, params, ...} => 
            HEADGOAL (EVERY' [
              Method.insert_tac ctxt [nth subprems 0],
              etac ctxt allE,
              etac ctxt impE,
              rtac ctxt (infer_instantiate' ctxt [NONE, SOME (snd (nth params 1))] exI),
              EqSubst.eqsubst_tac ctxt [1] [F_rel_map1],
              EqSubst.eqsubst_tac ctxt [1] [F_rel_map2],
              rtac ctxt F_rel_refl_strong,
              dtac ctxt (subsetD OF [nth subprems 1] RS @{thm Collect_case_prodD}),
              assume_tac ctxt,
              dtac ctxt (subsetD OF [nth subprems 2] RS @{thm Collect_case_prodD}),
              rtac ctxt sym,
              assume_tac ctxt,

              etac ctxt exE,
              EqSubst.eqsubst_tac ctxt [0] [unfold_map_comp],
              EqSubst.eqsubst_tac ctxt [1, 2] [switch id_o o_id],
              EqSubst.eqsubst_tac ctxt [0] [fold_map_comp],
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
  apply (tactic \<open>mk_nonrep2_map_F_tac @{thm nonrep2_def} @{thm sameShape1_def} @{thm F.map_comp} 
    @{thm F.mr_rel_map(1)} @{thm mr_rel_F_def} @{thm F.rel_compp} @{thm F.rel_Grp} @{thm F.map_id}
    @{thm F.in_rel} @{thm F.rel_map(1)} @{thm F.rel_map(2)} @{thm F.rel_refl_strong}
    @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)
    apply (elim exE)
    apply (subst F.map_comp[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound])
    apply (subst (1) trans[OF o_id id_o[symmetric]])
    apply (subst (1 2 4) trans[OF id_o o_id[symmetric]])
    apply (subst F.map_comp[OF supp_id_bound bij_id supp_id_bound prems(1,2,3), symmetric])
    apply (drule iffD1[OF F.mr_rel_map(1)[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound]])
    apply (subst (asm) (1 2) trans[OF id_o o_id[symmetric]])
    apply (subst (asm) Grp_UNIV_id)
    apply (subst (asm) trans[OF OO_eq eq_OO[symmetric]])
    apply (subst (asm) trans[OF eq_OO OO_eq [symmetric]])
    apply (subst (asm) (1 2) eq_alt)
    apply (unfold mr_rel_F_def o_id F.rel_compp F.rel_Grp F.map_id)
    apply (unfold eqTrueI[OF subset_UNIV] simp_thms(21) UNIV_def[symmetric] id_o)
    apply (unfold Grp_UNIV_id OO_def Grp_def eqTrueI[OF UNIV_I] simp_thms(21))
    apply (subst (asm) id_apply)
    apply (erule exE)
    apply (erule conjE)
    apply (drule iffD1[OF F.in_rel[OF prems(1,2,3)]])
    apply (insert prems(4)[unfolded nonrep2_def sameShape1_def mr_rel_F_def F.map_id])
    apply (erule exE)
    apply (erule conjE)
    apply (erule CollectE)
    apply (erule conjE)
    apply (erule conjE)
    apply (hypsubst_thin)
    subgoal premises subprems for x' R y z
      apply (insert subprems(1))
      apply (erule allE)
      apply (erule impE)
(* this instantiation of R is not really necessary, but it feels better to have it concretely *)
       apply (rule exI[of _ R])
       apply (subst F.rel_map(1))
       apply (subst F.rel_map(2))
       apply (rule F.rel_refl_strong)
        apply (drule subsetD[OF subprems(2), THEN Collect_case_prodD])
        apply (assumption)
       apply (drule subsetD[OF subprems(3), THEN Collect_case_prodD])
       apply (rule sym)
       apply (assumption)

      apply (elim exE)
      apply (subst F.map_comp[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound])
      apply (subst (1 2) trans[OF id_o o_id[symmetric]])
      apply (subst F.map_comp[OF supp_id_bound bij_id supp_id_bound prems(1,2,3), symmetric])
      apply (rule exI)
      apply (drule arg_cong)
      apply (assumption)
      done
    done
  done

ML\<open>
open BNF_Util BNF_Tactics

fun mk_nonrep2_map_F_rev_tac nonrep_def sameShape_def F_mr_rel_map1 F_mr_rel_map2 F_mr_rel_map3 F_map_comp F_rel_eq 
  F_mr_rel_id rel_F_exchange F_mr_rel_flip F_mr_rel_mono_strong0 F_mr_rel_Grp ctxt = 
  HEADGOAL (Subgoal.FOCUS 
    (fn {prems, context = ctxt, ...} => 
      let
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
          EqSubst.eqsubst_asm_tac ctxt [2] [switch @{thm o_id} @{thm id_o}],
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms Grp_UNIV_id},
          EqSubst.eqsubst_asm_tac ctxt [0] [switch @{thm eq_OO} @{thm OO_eq}],
          EqSubst.eqsubst_asm_tac ctxt [0] [switch @{thm OO_eq} @{thm eq_OO}],
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms eq_alt},
          EqSubst.eqsubst_asm_tac ctxt [0] [F_mr_rel_map1 RS sym] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          Method.insert_tac ctxt [unfold_thms ctxt [nonrep_def, sameShape_def] (nth prems 2)],
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
          rtac ctxt (unfold_thms ctxt @{thms inv_id} (F_mr_rel_flip OF @{thms bij_id supp_id_bound bij_id supp_id_bound}) RS iffD1),
          EqSubst.eqsubst_asm_tac ctxt [0] [F_mr_rel_map3] THEN_ALL_NEW
            TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
          EqSubst.eqsubst_asm_tac ctxt [1, 2, 3, 4] @{thms Grp_def},
          EqSubst.eqsubst_asm_tac ctxt [0] [@{thm inv_o_simp1} OF @{thms bij_id}],
          EqSubst.eqsubst_asm_tac ctxt [0] [@{thm inv_o_simp1} OF [(nth prems 0)]],
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms id_apply},
          K (unfold_thms_tac ctxt [eqTrueI OF @{thms UNIV_I}, @{thm simp_thms(21)}]),
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms eq_commute},
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms eq_OO},
          K (unfold_thms_tac ctxt @{thms conversep_def}),
          etac ctxt (rotate_prems 6 F_mr_rel_mono_strong0) THEN_ALL_NEW
            TRY o resolve_tac ctxt (ballI:: @{thms supp_id_bound bij_id}) THEN_ALL_NEW
            TRY o resolve_tac ctxt [refl, ballI] THEN_ALL_NEW
            TRY o rtac ctxt impI,
          rotate_tac 2,
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms eq_commute},
          assume_tac ctxt,
          K (unfold_thms_tac ctxt @{thms OO_def}),
          assume_tac ctxt,
          etac ctxt thin_rl,
          EqSubst.eqsubst_asm_tac ctxt [0] [@{thm Grp_UNIV_def} RS sym],
          rtac ctxt exI,
          EqSubst.eqsubst_asm_tac ctxt [0] @{thms eq_alt}
        ]) THEN
        unfold_thms_tac ctxt [F_mr_rel_Grp OF @{thms supp_id_bound bij_id supp_id_bound}] THEN
        unfold_thms_tac ctxt ([eqTrueI OF @{thms subset_UNIV}, eqTrueI OF @{thms UNIV_I}, @{thm UNIV_def} RS sym] @ 
          @{thms simp_thms(21) Grp_def}) THEN
        HEADGOAL (assume_tac ctxt)
      end)
  ctxt)
\<close>

(* Here we need pullback preservation: *)
lemma nonrep2_map_F_rev:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 (map_F id u id g x)"
  shows "nonrep2 x"
  using assms apply -
  apply (tactic \<open>mk_nonrep2_map_F_rev_tac @{thm nonrep2_def} @{thm sameShape1_def} @{thm F.mr_rel_map(1)}
    @{thm F.mr_rel_map(2)} @{thm F.mr_rel_map(3)} @{thm F.map_comp} @{thm F.rel_eq} @{thm F.mr_rel_id} @{thm rel_F_exchange} 
    @{thm F.mr_rel_flip} @{thm F.mr_rel_mono_strong0} @{thm F.mr_rel_Grp} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)

  subgoal premises prems
    thm F.mr_rel_map(2)[OF supp_id_bound bij_id supp_id_bound supp_id_bound, rotated 2]
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)
    apply (erule exE)
    apply (frule F.mr_rel_map(2)[rotated -1]; (rule prems supp_id_bound bij_id)?)
    apply (rotate_tac)
    apply (subst (asm) (2) trans[OF o_id id_o[symmetric]])
    apply (subst (asm) Grp_UNIV_id)
    apply (subst (asm) trans[OF eq_OO OO_eq[symmetric]])
    apply (subst (asm) trans[OF OO_eq eq_OO[symmetric]])
    apply (subst (asm) eq_alt)
    apply (subst (asm) F.mr_rel_map(1)[symmetric]; (rule prems supp_id_bound bij_id)?)
    apply (insert prems(3)[unfolded nonrep2_def sameShape1_def])
    apply (elim allE impE)
     apply (rule exI)
     apply (assumption)

    apply (erule thin_rl)
    apply (erule exE)
    apply (subst (asm) F.map_comp; (rule prems supp_id_bound bij_id)?)
    apply (unfold o_id id_o)
    apply (subst (asm) (1) F.rel_eq[symmetric])
    apply (unfold F.mr_rel_id)
    apply (drule iffD1[OF F.mr_rel_map(1), rotated -1]; (rule prems supp_id_bound bij_id)?)
    apply (unfold id_o OO_eq)

    apply (drule rel_F_exchange[rotated])
     apply (rule iffD1[OF F.mr_rel_flip[OF bij_id supp_id_bound bij_id supp_id_bound, unfolded inv_id]])
    apply (subst (asm) F.mr_rel_map(3); (rule prems supp_id_bound bij_id)?)
    apply (subst (asm) (1 2 3 4) Grp_def)
     apply (subst (asm) inv_o_simp1[OF bij_id])
     apply (subst (asm) inv_o_simp1[OF u(1)])
     apply (subst (asm) id_apply)
     apply (unfold eqTrueI[OF UNIV_I] simp_thms(21))
     apply (subst (asm) eq_commute)
     apply (subst (asm) eq_OO)
     apply (unfold conversep_def)
     apply (elim F.mr_rel_mono_strong0[rotated 6]; (rule supp_id_bound bij_id)?)
        apply (rule ballI; rule refl)
       apply (rule ballI; rule refl)
      apply (intro ballI impI)
      apply (rotate_tac 2)
      apply (subst (asm) eq_commute)
      apply (assumption)
     apply (intro ballI impI)
     apply (unfold OO_def)
     apply (assumption)

    apply (erule thin_rl)
    apply (subst (asm) Grp_UNIV_def[symmetric])
    apply (rule exI)
    apply (subst (asm) eq_alt)
    apply (unfold F.mr_rel_Grp[OF supp_id_bound bij_id supp_id_bound])
    apply (unfold eqTrueI[OF subset_UNIV] eqTrueI[OF UNIV_I] UNIV_def[THEN sym] simp_thms(21) Grp_def)
    apply (assumption)
    done
  done


lemma nonrep2_mapF_bij: (* TODO *)
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and g::"'a3\<Rightarrow>'a3"
  assumes g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F id id g id x)" (is "nonrep2 ?x'")
  using assms apply -
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)
    apply (erule exE)
    subgoal premises subprems for y' R'
      apply (insert subprems)
      apply (drule iffD1[OF F.mr_rel_map(1)[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound]])
      apply (unfold o_id)
  apply (subst (asm) Grp_UNIV_id)
  apply (subst (asm) (2) conversep_eq[symmetric])
  apply (subst (asm) (2) Grp_UNIV_id[symmetric])
      thm 
        subprems[THEN iffD1[OF F.mr_rel_map(1)[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound], unfolded o_id]]
        F.mr_rel_map(3)[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound, symmetric, 
            unfolded inv_id o_id]
        F.mr_rel_map(3)[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound,
              of "Grp g OO R' OO conversep (Grp g)" _ _ "inv g" id, symmetric,
              unfolded inv_id o_id, of "(=)" x y']
        F.mr_rel_map(3)[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound,
              of "Grp g OO R' OO conversep (Grp g)" _ _ "inv g" id, symmetric,
              unfolded Grp_UNIV_id conversep_eq OO_eq inv_id comp_id relcompp_assoc converse_relcompp[symmetric] Grp_o[symmetric]
              inv_o_simp2[OF g], of "(=)" x y']

      thm Grp_UNIV_id conversep_eq OO_eq inv_id comp_id relcompp_assoc converse_relcompp[symmetric] Grp_o[symmetric]
              inv_o_simp2[OF g]
      apply (drule iffD1[OF F.mr_rel_map(3)[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound,
              of "Grp g OO R' OO conversep (Grp g)" _ _ "inv g" id, symmetric,
              unfolded Grp_UNIV_id conversep_eq OO_eq inv_id comp_id relcompp_assoc converse_relcompp[symmetric] Grp_o[symmetric]
              inv_o_simp2[OF g]]])
      thm x[unfolded nonrep2_def sameShape1_def, rule_format, OF exI]
      apply (drule x[unfolded nonrep2_def sameShape1_def, rule_format, OF exI])
      apply (erule exE)
      subgoal premises subprems2 for f
        apply (subst F.map_id[symmetric])
        apply (subst (7 9 13) o_id[symmetric])
        apply (subst inv_o_simp2[OF g, symmetric])
        apply (fold F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound])
        apply (subst subprems2)
        apply (subst (20) o_id[symmetric])
        apply (subst inv_o_simp1[OF g, symmetric])
        apply (unfold F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound])
        apply (subst (1 2) o_assoc)
        apply (rule exI)
        apply (rule refl)
        done
      done
    done
  done
  sorry

lemma "(Grp id OO (=)) = ((=) OO (Grp id)\<inverse>\<inverse>)"
  apply (rule refl)

ML \<open>
open BNF_Util BNF_Tactics

fun mk_nonrep2_mapF_bij_2_tac nonrep2_mapF_bij nonrep2_map_F F_map_comp ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
    let val nr_prems = length prems in
      HEADGOAL (rtac ctxt (unfold_thms ctxt ((F_map_comp OF ((take (nr_prems-2) prems) @ @{thms supp_id_bound bij_id supp_id_bound})) :: @{thms id_o o_id}) 
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
  apply (tactic \<open>mk_nonrep2_mapF_bij_2_tac @{thm nonrep2_mapF_bij} @{thm nonrep2_map_F} @{thm F.map_comp} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (rule nonrep2_mapF_bij[OF prems(4) nonrep2_map_F[OF prems(1,2,3,5)], 
          unfolded F.map_comp[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound] id_o o_id])
    done
  done


typedef ('a1::var,'a2::var,'a3::var,'a4) F' = "{x :: ('a1,'a2,'a3,'a4) F. nonrep2 x}"
  apply (unfold mem_Collect_eq nonrep2_def sameShape1_def mr_rel_F_def F.map_id id_apply)
  apply (unfold id_def[symmetric])
  by (rule ex_nonrep)

definition set1_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a1 set" where "set1_F' = set1_F o Rep_F'"
definition set2_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a2 set" where "set2_F' = set2_F o Rep_F'"
definition set3_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a3 set" where "set3_F' = set3_F o Rep_F'"
definition set4_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a4 set" where "set4_F' = set4_F o Rep_F'"

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV :: 'a set| then f else id"

definition map_F' :: "('a1::var \<Rightarrow> 'a1) \<Rightarrow> ('a2::var \<Rightarrow> 'a2) \<Rightarrow> ('a3::var \<Rightarrow> 'a3) \<Rightarrow> ('a4 \<Rightarrow> 'a4') 
  \<Rightarrow> ('a1,'a2,'a3,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F'"
  where "map_F' v u f g = Abs_F' o map_F (asSS v) (asSS (asBij u)) (asBij f) g o Rep_F'"

definition rrel_F' :: "('a4 \<Rightarrow> 'a4' \<Rightarrow> bool) \<Rightarrow> ('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F' \<Rightarrow> bool"
  where "rrel_F' R x x' = rrel_F (=) R (Rep_F' x) (Rep_F' x')"

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

lemma F'_map_id: "map_F' id id id id = id"
  apply (tactic \<open>mk_map_id_tac @{thm map_F'_def} @{thm F.map_id} @{thm Rep_F'_inverse} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  apply (unfold map_F'_def asSS_def asBij_def 
      eqTrueI[OF bij_id] eqTrueI[OF supp_id_bound] if_True)
  apply (rule ext)
  apply (unfold o_apply F.map_id Rep_F'_inverse)
  apply (unfold id_def)
  apply (rule refl)
  done


ML \<open>
open BNF_Util BNF_Tactics

fun mk_map_comp_tac map_F'_def Abs_F'_inverse Rep_F' nonrep2_mapF_bij_2 F_map_comp0 ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems as [supp_u1, supp_v1, bij_u2, supp_u2, bij_v2, supp_v2, bij_u3, _, bij_v3, _],
      context = ctxt, ...} =>
    let
      val _ = prems |> map @{print tracing}
      val supp_comp = @{thm eqTrueI[OF supp_comp_bound[OF _ _ infinite_UNIV]]}
      val bij_comp = @{thm eqTrueI[OF bij_comp]}
    in
      unfold_thms_tac ctxt ([map_F'_def,
        supp_comp OF [supp_u1, supp_v1],
        supp_comp OF [supp_u2, supp_v2],
        bij_comp OF [bij_u2, bij_v2],
        bij_comp OF [bij_u3, bij_v3]] @ map (fn thm => thm RS eqTrueI) prems @
        @{thms asSS_def asBij_def if_True}) THEN
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [F_map_comp0 OF [supp_u1, bij_u2, supp_u2, supp_v1, bij_v2, supp_v2]] THEN
      unfold_thms_tac ctxt [o_apply] THEN
      HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
        rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems),
        rtac ctxt refl])
    end) ctxt)
\<close>

lemma F'_map_comp1_:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  shows "map_F' (v1 o u1) (v2 o u2) (v3 o u3) (g o f) = map_F' v1 v2 v3 g o map_F' u1 u2 u3 f"
  using assms apply -
  apply (tactic \<open>mk_map_comp_tac @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.map_comp0} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold map_F'_def asBij_def asSS_def
        eqTrueI[OF supp_comp_bound[OF assms(1,2) infinite_UNIV]]
        eqTrueI[OF supp_comp_bound[OF assms(4,6) infinite_UNIV]]
        eqTrueI[OF bij_comp[OF assms(3,5)]]
        eqTrueI[OF bij_comp[OF assms(7,9)]]
        eqTrueI[OF assms(5)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(1)] eqTrueI[OF assms(4)] eqTrueI[OF assms(6)]
        eqTrueI[OF assms(7)] eqTrueI[OF assms(9)]
        if_True)
    apply (rule ext)
    apply (unfold F.map_comp0[OF assms(1,3,4,2,5,6)])
    apply (unfold o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
      (*apply (rule  nonrep2_mapF_bij_2[OF assms(1,3,4,7)])*)
     apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
    apply (rule refl)
    done
  done


(* This tactic is applicable to all 4 of the following <F'_setx_map_> lemmas*)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_set_map_tac set_F'_def map_F'_def Abs_F'_inverse Rep_F' nonrep2_mapF_bij_2 F_set_map ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems as [supp_u1, bij_u2, supp_u2, _, _],
      context = ctxt, ...} =>
    let
      val _ = prems |> map @{print tracing}
    in
      unfold_thms_tac ctxt ([set_F'_def, map_F'_def] @ map (fn thm => thm RS eqTrueI) prems @
        @{thms asSS_def asBij_def if_True o_apply}) THEN
      HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
        rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems),
        rtac ctxt (F_set_map OF [supp_u1, bij_u2, supp_u2])])
    end) ctxt)
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
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] o_apply if_True)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
      (*apply (rule nonrep2_mapF_bij_2[OF assms(1,2,3,4)])*)
     apply (rule nonrep2_mapF_bij_2; (rule assms Rep_F'[unfolded mem_Collect_eq])?)
    apply (rule F.set_map(1)[OF assms(1,2,3)])
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


ML \<open>
open BNF_Util BNF_Tactics

fun mk_map_cong_tac map_F'_def set1_F'_def set2_F'_def set3_F'_def set4_F'_def  F_map_cong ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems as [supp_u1, supp_v1, bij_u2, supp_u2, bij_v2, supp_v2, _, _, _, _,
      eq_set1, eq_set2, eq_set3, eq_set4],
      context = ctxt, ...} =>
    let
      val _ = prems |> map @{print tracing}
    in
      unfold_thms_tac ctxt ([map_F'_def] @ map (fn thm => thm RS eqTrueI) prems @
        @{thms asSS_def asBij_def if_True o_apply}) THEN
      HEADGOAL (EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [F_map_cong OF [supp_u1, bij_u2, supp_u2, supp_v1, bij_v2, supp_v2]],
        rtac ctxt refl,
        etac ctxt (bspec OF [unfold_thms ctxt [set1_F'_def, @{thm o_apply}] eq_set1]),
        etac ctxt (bspec OF [unfold_thms ctxt [set2_F'_def, @{thm o_apply}] eq_set2]),
        etac ctxt (bspec OF [unfold_thms ctxt [set3_F'_def, @{thm o_apply}] eq_set3]),
        etac ctxt (bspec OF [unfold_thms ctxt [set4_F'_def, @{thm o_apply}] eq_set4]),
        rtac ctxt refl])
    end) ctxt)
\<close>

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
  apply (tactic \<open>mk_map_cong_tac @{thm map_F'_def} @{thm set1_F'_def} @{thm set2_F'_def} 
    @{thm set3_F'_def} @{thm set4_F'_def} @{thm F.map_cong} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold map_F'_def asSS_def asBij_def 
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] eqTrueI[OF assms(5)] 
        eqTrueI[OF assms(6)] eqTrueI[OF assms(7)] eqTrueI[OF assms(9)] if_True o_apply)
    apply (subst F.map_cong[OF prems(1,3,4,2,5,6)])
         apply (rule refl)
        apply (erule bspec[OF prems(11)[unfolded set1_F'_def o_apply]])
       apply (erule bspec[OF prems(12)[unfolded set2_F'_def o_apply]])
      apply (erule bspec[OF prems(13)[unfolded set3_F'_def o_apply]])
     apply (erule bspec[OF prems(14)[unfolded set4_F'_def o_apply]])
    apply (rule refl)
    done
  done


(* This tactic is applicable to all 4 of the following <F'_setx_bd> lemmas*)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_set_bd_tac set_F'_def F_set_bd ctxt =
    unfold_thms_tac ctxt [set_F'_def, o_apply] THEN
    HEADGOAL (rtac ctxt F_set_bd)
\<close>

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o natLeq"
  apply (tactic \<open>mk_set_bd_tac @{thm set1_F'_def} @{thm F.set_bd(1)} @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  apply (unfold set1_F'_def o_apply)
  apply (rule F.set_bd(1))
  done
lemma F'_set2_bd: "\<And>b. |set2_F' b| <o natLeq"
  apply (tactic \<open>mk_set_bd_tac @{thm set2_F'_def} @{thm F.set_bd(2)} @{context}\<close>)
  done
lemma F'_set3_bd: "\<And>b. |set3_F' b| <o natLeq"
  apply (tactic \<open>mk_set_bd_tac @{thm set3_F'_def} @{thm F.set_bd(3)} @{context}\<close>)
  done
lemma F'_set4_bd: "\<And>b. |set4_F' b| <o natLeq"
  apply (tactic \<open>mk_set_bd_tac @{thm set4_F'_def} @{thm F.set_bd(4)} @{context}\<close>)
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rel_comp_leq_tac rrel_F'_def F_rel_compp ctxt =
 HEADGOAL (Subgoal.FOCUS
    (fn {context = ctxt, ...} => print_tac @{context} "0" THEN
      HEADGOAL (rtac ctxt @{thm predicate2I}) THEN print_tac @{context} "1" THEN
      HEADGOAL (etac ctxt @{thm relcomppE}) THEN print_tac @{context} "2" THEN
      unfold_thms_tac ctxt [rrel_F'_def] THEN print_tac @{context} "3" THEN
      HEADGOAL (EqSubst.eqsubst_tac ctxt [1] (@{thms eq_OO[symmetric]})) THEN print_tac @{context} "4" THEN
      HEADGOAL (EqSubst.eqsubst_tac ctxt [1] ([F_rel_compp])) THEN print_tac @{context} "5" THEN
      unfold_thms_tac ctxt [rrel_F'_def] THEN print_tac @{context} "6" THEN
      HEADGOAL (rtac ctxt @{thm relcomppI} THEN_ALL_NEW assume_tac ctxt)
    ) ctxt)
  
\<close>

lemma F'_rel_comp_leq_: "rrel_F' Q OO rrel_F' R \<le> rrel_F' (Q OO R)"
  apply (tactic \<open>mk_rel_comp_leq_tac @{thm rrel_F'_def} @{thm F.rel_compp} @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (rule predicate2I)
    apply (erule relcomppE)
    apply (unfold rrel_F'_def) (* Somehow this only unfolds the goal in the tactic *)
    apply (subst (1) eq_OO[symmetric])
    apply (subst (1) F.rel_compp)
      (*apply (unfold rrel_F'_def)*)
    apply (rule relcomppI; (assumption))
    done
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rrel_F_map_F3_tac F_rel_map F_rel_mono_strong Grp_def ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {context = ctxt, ...} =>
      unfold_thms_tac ctxt ([F_rel_map, Grp_def, eqTrueI OF @{thms UNIV_I}] @ @{thms id_apply simp_thms(21)}) THEN
      HEADGOAL (rtac ctxt @{thm iffI}) THEN
      ALLGOALS (EVERY' [etac ctxt F_rel_mono_strong, etac ctxt sym, assume_tac ctxt])
    ) ctxt)
\<close>

lemma rrel_F_map_F3:
  fixes x :: "('a :: var,'b :: var,'c,'d) F"
  shows "rrel_F (Grp (f :: 'c \<Rightarrow> 'c)) R x y = rrel_F (=) R (map_F id id f id x) y"
  apply (tactic \<open>mk_rrel_F_map_F3_tac @{thm F.rel_map(1)} @{thm F.rel_mono_strong} @{thm Grp_def} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold F.rel_map(1) Grp_def id_apply eqTrueI[OF UNIV_I] simp_thms(21))
    apply (rule iffI)
     apply (erule F.rel_mono_strong, erule sym, assumption)+
    done
  done


ML \<open>
open BNF_Util BNF_Tactics

fun mk_asSS_tac ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} =>
      unfold_thms_tac ctxt @{thms asSS_def} THEN
      HEADGOAL (rtac ctxt @{thm if_P}) THEN
      HEADGOAL (rtac ctxt (nth prems 0))
    ) ctxt)
\<close>

lemma asSS: "|supp u| <o |UNIV :: 'a set| \<Longrightarrow> asSS (u :: 'a \<Rightarrow> 'a) = u"
  apply (tactic \<open>mk_asSS_tac @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold asSS_def)
    apply (rule if_P) 
    apply (rule prems)
    done
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_in_rel_tac rrel_F'_def set4_F'_def map_F'_def Abs_F'_inverse Rep_F' nonrep2_mapF_bij_2 
  rrel_F_map_F3 F_in_rel F_map_comp nonrep2_map_F_rev F_set_map3 F_set_map4 Rep_F'_inverse F_map_cong cx ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt,...} =>
        unfold_thms_tac ctxt ([rrel_F'_def, set4_F'_def, map_F'_def, o_apply] @ @{thms asSS_def asBij_def if_True} @ 
          map (fn thm => thm RS eqTrueI) (prems @ @{thms supp_id_bound bij_id})) THEN
        HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse])THEN
        HEADGOAL (rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems)) THEN
        HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [(unfold_thms ctxt ((F_map_comp OF ((take 3 prems) @ @{thms supp_id_bound bij_id supp_id_bound})):: @{thms id_o o_id})
          (trans OF [rrel_F_map_F3 RS sym, F_in_rel OF (take 3 prems)]))]) THEN
        unfold_thms_tac ctxt ((eqTrueI OF @{thms UNIV_I}):: @{thms Grp_def simp_thms(21)}) THEN
        HEADGOAL (rtac ctxt iffI) THEN
        (* 1st Subgoal *)
        REPEAT_DETERM_N 5 (HEADGOAL (eresolve_tac ctxt [exE, conjE, CollectE])) THEN
        HEADGOAL (Subgoal.FOCUS
          (fn {prems = subprems, context = ctxt, params, ...} =>
            let
              val _ = subprems |> map @{print tracing};
              val _ = params |> map @{print tracing};
            in
              (* setup *)
              HEADGOAL (EVERY' [
                rtac ctxt exI,
                EqSubst.eqsubst_tac ctxt [1, 2, 3] [Abs_F'_inverse],
                Method.insert_tac ctxt [unfold_thms ctxt [(nth subprems 0 RS sym)] (infer_instantiate' ctxt [SOME cx] Rep_F')],
                EqSubst.eqsubst_asm_tac ctxt [8] [@{thm id_o} RS sym],
                EqSubst.eqsubst_asm_tac ctxt [4, 6, 14] [@{thm o_id} RS sym],
                EqSubst.eqsubst_asm_tac ctxt [0] [F_map_comp OF @{thms supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound} RS sym],
                dtac ctxt (nonrep2_map_F_rev OF @{thms bij_id supp_id_bound}),
                assume_tac ctxt
              ]) THEN
              (* solve *)
              HEADGOAL (EVERY' [
                EqSubst.eqsubst_tac ctxt [1, 2] [F_map_comp] THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms bij_id supp_id_bound}),
                K (unfold_thms_tac ctxt @{thms id_o o_id}),
                rtac ctxt conjI,
                EqSubst.eqsubst_tac ctxt [0] [F_set_map4 OF @{thms supp_id_bound bij_id supp_id_bound}],
                EqSubst.eqsubst_tac ctxt [0] @{thms image_id},
                resolve_tac ctxt subprems,
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
            end) 
          ctxt) THEN
        (* 2nd Subgoal *)
        REPEAT_DETERM_N 3 (HEADGOAL (eresolve_tac ctxt [exE, conjE])) THEN
        HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
        HEADGOAL (Subgoal.FOCUS
          (fn {prems = subprems, context = ctxt, ...} =>
            let
              val _ = subprems |> map @{print tracing};
            in
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
                EqSubst.eqsubst_tac ctxt [0] [F_map_comp OF @{thms supp_id_bound bij_id supp_id_bound}] THEN_ALL_NEW
                  TRY o resolve_tac ctxt prems,
                K (unfold_thms_tac ctxt @{thms o_id}),
                EqSubst.eqsubst_tac ctxt [1, 2] @{thms o_def},
                rtac ctxt F_map_cong THEN_ALL_NEW
                  TRY o resolve_tac ctxt (refl::prems),
                rtac ctxt @{thm snd_conv},
                rtac ctxt CollectI,
                EqSubst.eqsubst_tac ctxt [0] [F_set_map3 OF @{thms supp_id_bound bij_id supp_id_bound}],
                EqSubst.eqsubst_tac ctxt [0] [F_set_map4 OF @{thms supp_id_bound bij_id supp_id_bound}],
                EqSubst.eqsubst_tac ctxt [0] @{thms image_ident},
                rtac ctxt conjI,
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
                resolve_tac ctxt subprems,
                EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                  TRY o resolve_tac ctxt @{thms supp_id_bound bij_id},
                K (unfold_thms_tac ctxt @{thms o_def id_def fst_conv}),
                rtac ctxt refl
              ])
            end) 
          ctxt) 
    ) ctxt)
\<close>


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
  apply (tactic \<open>mk_in_rel_tac @{thm rrel_F'_def} @{thm set4_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm rrel_F_map_F3} @{thm F.in_rel}
    @{thm F.map_comp} @{thm nonrep2_map_F_rev} @{thm F.set_map(3)} @{thm F.set_map(4)} @{thm Rep_F'_inverse} @{thm F.map_cong}
    @{cterm x} @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold rrel_F'_def set4_F'_def map_F'_def asSS_def asBij_def if_True 
        eqTrueI[OF prems(1)] eqTrueI[OF prems(2)] eqTrueI[OF prems(3)] eqTrueI[OF prems(4)] 
        eqTrueI[OF supp_id_bound] eqTrueI[OF bij_id] o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
     apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
    apply (subst trans[OF rrel_F_map_F3[symmetric] F.in_rel[OF prems(1,2,3)],
          unfolded F.map_comp[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound] id_o o_id])
    apply (unfold Grp_def eqTrueI[OF UNIV_I] simp_thms(21))
    apply (rule iffI)
     apply (erule exE)
     apply (erule conjE)
     apply (erule conjE)
     apply (erule CollectE)
     apply (erule conjE)
    subgoal premises subprems for z
      (*     apply (tactic \<open>
        let
          val ctxt = @{context};
          val cz = @{cterm z};
          val z = Thm.term_of cz;
          val zT = fastype_of z;
          val which = 0;
          val Abs_F' = @{term Abs_F'}
          val mrbnf = MRBNF_Def.mrbnf_of ctxt @{type_name F} |> the;
          val subst = Sign.typ_match (Proof_Context.theory_of ctxt)
            (MRBNF_Def.T_of_mrbnf mrbnf, zT) Vartab.empty;
          val deads = MRBNF_Def.deads_of_mrbnf mrbnf |> map (Envir.subst_type subst) |> @{print};
          val frees = MRBNF_Def.frees_of_mrbnf mrbnf |> map (Envir.subst_type subst) |> @{print};
          val bounds = MRBNF_Def.bounds_of_mrbnf mrbnf |> map (Envir.subst_type subst) |> @{print};
          val lives = MRBNF_Def.lives_of_mrbnf mrbnf |> map (Envir.subst_type subst) |> @{print};
          val map_F = MRBNF_Def.mk_map_comb_of_mrbnf deads
            (map_index (uncurry (fn i => if i = which then BNF_Util.fst_const else HOLogic.id_const)) lives)
            (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
            mrbnf $ z |> @{print};
          val Ts = fastype_of map_F |> dest_Type |> snd;
          val Us = domain_type (fastype_of Abs_F') |> dest_Type |> snd;
          val ct = Thm.cterm_of ctxt (subst_atomic_types (Us ~~ Ts) Abs_F' $ map_F) |> @{print};
        in
          HEADGOAL (BNF_Util.rtac ctxt (infer_instantiate' ctxt [NONE, SOME ct] exI))
        end
        \<close>) *)
      apply (rule exI)
      apply (subst (1 2 3) Abs_F'_inverse[unfolded mem_Collect_eq])
       apply (insert Rep_F'[of x, unfolded mem_Collect_eq subprems(1)[symmetric]]) []
       apply (subst (asm) (8) id_o[symmetric])
       apply (subst (asm) (4 6 14) o_id[symmetric])
       apply (subst (asm) F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound, symmetric])
       apply (drule nonrep2_map_F_rev[OF bij_id supp_id_bound])
       apply (assumption)

      apply (subst (1 2) F.map_comp; (rule supp_id_bound bij_id prems(1,2,3))?)
      apply (unfold o_id id_o)
      apply (rule conjI)
       apply (subst F.set_map(4)[OF supp_id_bound bij_id supp_id_bound])
       apply (subst image_id)
       apply (rule subprems)
      apply (subst (2 4) Rep_F'_inverse[symmetric])
      apply (rule conjI)
       apply (rule arg_cong[OF subprems(1)])
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

        prefer 3(* subgoal 3 is solvable without the exI instantiation and it transforms "?z" 
          so that the other 2 subgoals are solvable as well*)
        apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
         apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
        apply (subst F.map_comp[OF supp_id_bound bij_id supp_id_bound]; (rule prems(1,2,3))?)
        apply (unfold o_id)
        apply (subst (1 2) o_def)
        apply (rule F.map_cong; (rule prems(1,2,3) refl)?)
        apply (rule snd_conv)

       apply (rule CollectI)
       apply (subst F.set_map(3)[OF supp_id_bound bij_id supp_id_bound])
       apply (subst F.set_map(4)[OF supp_id_bound bij_id supp_id_bound])
       apply (subst image_ident)
       apply (rule conjI) 
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
       apply (rule subprems)

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

ML \<open>
open BNF_Util BNF_Tactics

fun mk_is_mrbnf_tac F'_map_id F'_map_comp1 F'_map_cong F'_set1_map F'_set2_map F'_set3_map F'_set4_map
    F'_set1_bd F'_set2_bd F'_set3_bd F'_set4_bd F'_rel_comp_leq F'_in_rel ctxt = 
  HEADGOAL (rtac ctxt F'_map_id) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt F'_map_comp1 THEN_ALL_NEW resolve_tac ctxt prems)
    ) ctxt) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt F'_map_cong THEN_ALL_NEW resolve_tac ctxt (ballI :: prems)) THEN
      ALLGOALS (resolve_tac ctxt prems) THEN
      ALLGOALS (assume_tac ctxt) 
    ) ctxt) THEN
  REPEAT_DETERM_N 4 (HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [o_apply] THEN
      HEADGOAL (resolve_tac ctxt (map (fn thm => thm OF prems) [F'_set1_map, F'_set2_map, F'_set3_map, F'_set4_map]))
    ) ctxt)) THEN
  HEADGOAL (rtac ctxt @{thm infinite_regular_card_order_natLeq}) THEN
  REPEAT_DETERM_N 4 (HEADGOAL (
    resolve_tac ctxt [F'_set1_bd, F'_set2_bd, F'_set3_bd, F'_set4_bd])) THEN
  HEADGOAL (rtac ctxt F'_rel_comp_leq) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt (F'_in_rel OF prems))
    ) ctxt)
\<close>



mrbnf "('a::var, 'b::var, 'c::var, 'd) F'"
  map: map_F'
  sets: free: set1_F' bound: set2_F' bound: set3_F' live: set4_F'
  bd: natLeq
  rel: rrel_F'
  var_class: var
               apply (tactic \<open>mk_is_mrbnf_tac 
  @{thm F'_map_id} @{thm F'_map_comp1_} @{thm F'_map_cong_}
  @{thm F'_set1_map_} @{thm F'_set2_map_} @{thm F'_set3_map_} @{thm F'_set4_map_}
  @{thm F'_set1_bd} @{thm F'_set2_bd} @{thm F'_set3_bd} @{thm F'_set4_bd}
  @{thm F'_rel_comp_leq_} @{thm F'_in_rel} @{context}
   THEN print_tac @{context} "done" THEN no_tac\<close>)
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