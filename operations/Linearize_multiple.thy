theory Linearize_multiple
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

typedecl ('a, 'b, 'c, 'd, 'e) F
consts map_F :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> ('b :: var \<Rightarrow> 'b) \<Rightarrow>
  ('c \<Rightarrow> 'c') \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('e \<Rightarrow> 'e') \<Rightarrow> ('a, 'b, 'c, 'd, 'e) F \<Rightarrow> ('a, 'b, 'c', 'd', 'e') F"
consts set1_F :: "('a :: var, 'b :: var, 'c, 'd, 'e) F \<Rightarrow> 'a set"
consts set2_F :: "('a :: var, 'b :: var, 'c, 'd, 'e) F \<Rightarrow> 'b set"
consts set3_F :: "('a :: var, 'b :: var, 'c, 'd, 'e) F \<Rightarrow> 'c set"
consts set4_F :: "('a :: var, 'b :: var, 'c, 'd, 'e) F \<Rightarrow> 'd set"
consts set5_F :: "('a :: var, 'b :: var, 'c, 'd, 'e) F \<Rightarrow> 'e set"
consts rrel_F :: "('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'e' \<Rightarrow> bool) \<Rightarrow> ('a :: var, 'b :: var, 'c, 'd, 'e) F 
  \<Rightarrow> ('a, 'b, 'c', 'd', 'e') F \<Rightarrow> bool"

declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
mrbnf "('a :: var, 'b :: var, 'c, 'd, 'e) F"
  map: map_F
  sets: free: set1_F bound: set2_F live: set3_F live: set4_F live: set5_F
  bd: natLeq
  rel: rrel_F
  var_class: var
  sorry

(* we linearize this MRBNF on position 3 and 5*)
ML \<open>val lin_poses = [3, 5]\<close>

print_mrbnfs
declare [[ML_print_depth=10000]]
ML \<open>MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the \<close>

axiomatization where
  (* The next property assumes preservation of pullbacks on the third position. 
   NB: All MRBNFs already preserve _weak_ pullbacks, i.e., they satisfy the following property 
   without uniqueness.  *)
  F_rel_map_set2_strong: 
  "\<And> R S T (x :: ('a :: var,'b :: var,'c,'d,'e) F) y.
    rrel_F R S T x y =
      (\<exists>!z. set3_F z \<subseteq> {(x, y). R x y} \<and> set4_F z \<subseteq> {(x, y). S x y} \<and>
            set5_F z \<subseteq> {(x, y). T x y} \<and> map_F id id fst fst fst z = x \<and> map_F id id snd snd snd z = y)"
  and
  (* The next property assumes that nonrepetitive elements exist: *)
  ex_nonrep: "\<exists>x. \<forall>x'. (\<exists> R1 R2. rrel_F R1 (=) R2 x x') \<longrightarrow> (\<exists> f1 f2 . x' = map_F id id f1 id f2 x)"

lemma rrel_F_alt: "rrel_F top (=) top x y = (\<exists>R1 R2. rrel_F R1 (=) R2 x y)"
  (*pluses for the exE/exI*)
  apply (rule iffI)
  apply (rule exI)+
  apply (assumption)
   apply (erule exE)+
   apply (rule F.rel_mono_strong; 
      ((subst top_apply, subst top_apply, subst top_bool_def, rule TrueI)?, assumption?))
  done

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
  "rel_F id id R3 R4 R5 x y \<Longrightarrow> rel_F id id Q3 Q4 Q5 x y \<Longrightarrow> rel_F id id (inf R3 Q3) (inf R4 Q4) (inf R5 Q5) x y"
  by (tactic \<open>mk_F_strong_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm F.map_id} 
    @{thm mr_rel_F_def} @{thm F.mr_rel_mono_strong0} @{thm F_rel_map_set2_strong} @{thm F.in_rel} @{context} 
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

(* lin_pos dependent? *)
(* Another important consequence: the following "exchange"-property, which could be read: 
Since the atoms have a fixed position, we can permute the relations: *)
lemma rel_F_exchange: 
  fixes x :: "('a1::var,'a2::var,'a3,'a4,'a5) F" and x' :: "('a1,'a2,'a3','a4','a5') F"
  assumes "rel_F id id R3 R4 R5 x x'" and "rel_F id id Q3 Q4 Q5 x x'"
  shows "rel_F id id R3 Q4 R5 x x'" 
  using assms apply -
  by (tactic \<open>mk_rel_F_exchange_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) 
    @{thm F.mr_rel_mono_strong0} @{thm F_strong} @{context} 
    THEN print_tac @{context} "done"\<close>)

(* Then notion of two items having the same shape (w.r.t. the 3rd position): *)
(* these definitions are lin_pos dependent *)
definition sameShape1 :: "('a1::var,'a2::var,'a3,'a4,'a5) F \<Rightarrow> ('a1,'a2,'a3,'a4,'a5) F \<Rightarrow> bool" where 
  "sameShape1 x x' \<equiv> \<exists> R1 R2. rel_F id id R1 (=) R2 x x'"

definition nonrep2 :: "('a1::var,'a2::var,'a3,'a4,'a5) F \<Rightarrow> bool" where 
  "nonrep2 x \<equiv> \<forall> x'. sameShape1 x x' \<longrightarrow> (\<exists> f1 f2. x' = map_F id id f1 id f2 x)"

(* lin_pos dependent *)
lemma nonrep2_map_F:
  fixes x :: "('a1::var,'a2::var,'a3,'a4,'a5) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|"  and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 x"
  shows "nonrep2 (map_F v u id g id x)"
  using assms apply -
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)
    apply (elim exE)
    apply (subst F.map_comp; (rule prems bij_id supp_id_bound)?)
    apply (unfold trans[OF id_o o_id[symmetric]])
    apply (subst (3 5) trans[OF o_id id_o[symmetric]])
    apply (subst F.map_comp[THEN sym]; (rule prems bij_id supp_id_bound)?)
    apply (drule iffD1[OF F.mr_rel_map(1), rotated -1]; (rule prems bij_id supp_id_bound)?)
    apply (unfold trans[OF id_o o_id[symmetric]] Grp_UNIV_id)
    apply (unfold trans[OF OO_eq eq_OO[symmetric]])
    apply (subst (asm) (1 3) trans[OF eq_OO OO_eq [symmetric]])
    apply (unfold eq_alt)
    apply (subst Grp_UNIV_id)
    apply (unfold mr_rel_F_def o_id F.rel_compp F.rel_Grp)
    apply (unfold eqTrueI[OF subset_UNIV] simp_thms(21) UNIV_def[symmetric] id_o)
    apply (tactic \<open>unfold_thms_tac @{context} @{thms Grp_UNIV_id OO_def Grp_def eqTrueI[OF UNIV_I] simp_thms(21) id_apply}\<close>)
    apply (erule exE)
    apply (erule conjE)
    apply (drule F.in_rel[THEN iffD1, rotated -1]; (rule prems)?)
    apply (insert prems(4)[unfolded nonrep2_def sameShape1_def mr_rel_F_def F.map_id])
    apply (erule exE)
    apply (erule conjE)
    apply (erule CollectE)
    apply (erule conjE)
    apply (erule conjE)
    apply (erule conjE)
    apply (hypsubst_thin)
    subgoal premises subprems for x' R1 R2 y z
      thm subprems
      apply (insert subprems(1))
      apply (erule allE)
      apply (erule impE)
(* this instantiation of R is not really necessary, but it feels better to have it concretely *)
       apply (rule exI[of _ R1])
       apply (rule exI[of _ R2]) (*repeat for each lin_pos*)
      apply (subst F.rel_map)
       apply (subst F.rel_map)
       apply (rule F.rel_refl_strong)
         apply (drule subsetD[OF subprems(2), THEN Collect_case_prodD] 
            subsetD[OF subprems(3), THEN Collect_case_prodD]
            subsetD[OF subprems(4), THEN Collect_case_prodD]; 
                (assumption)?; (rule sym; assumption)?)+
      apply (elim exE)
      apply (subst F.map_comp; (rule prems bij_id supp_id_bound)?)
      apply (subst (1 2) trans[OF id_o o_id[symmetric]])
      apply (subst F.map_comp[THEN sym]; (rule prems bij_id supp_id_bound)?)
      apply (rule exI)
      apply (rule exI) (*repeat for each lin_pos*)
      apply (drule arg_cong)
      apply (assumption)
      done
    done
  done

(* Here we need pullback preservation: *)
lemma nonrep2_map_F_rev:
  fixes x :: "('a1::var,'a2::var,'a3,'a4,'a5) F" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'a4'"
  assumes u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 (map_F id u id g id x)"
  shows "nonrep2 x"
  using assms apply -
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)
    apply (erule exE)
    apply (erule exE) (*repeat for each lin_pos*)
    apply (frule F.mr_rel_map(2)[rotated -1]; (rule prems supp_id_bound bij_id)?)
    apply (rotate_tac)
    apply (subst (asm) (1 2) trans[OF o_id id_o[symmetric]]) (*1..nr_non_lives*)
    apply (subst (asm) (1 3) Grp_UNIV_id) (*lin_live_pos*)
    apply (unfold trans[OF eq_OO OO_eq[symmetric]])
    apply (subst (asm) (1 3) trans[OF OO_eq eq_OO[symmetric]]) (*lin_live_pos*)
    apply (subst (asm) (1 3) eq_alt) (*lin_live_pos*)
    apply (subst (asm) F.mr_rel_map(1)[symmetric]; (rule prems supp_id_bound bij_id)?)
    apply (insert prems(3)[unfolded nonrep2_def sameShape1_def]) (*lastprem*)
    apply (elim allE impE)
     apply (rule exI)
     apply (rule exI)
     apply (assumption)

    apply (erule thin_rl)
    apply (erule exE)
    apply (erule exE)
    apply (subst (asm) F.map_comp; (rule prems supp_id_bound bij_id)?)
    apply (unfold o_id id_o)
    apply (subst (asm) F.rel_eq[symmetric])
    apply (unfold F.mr_rel_id)
    apply (drule iffD1[OF F.mr_rel_map(1), rotated -1]; (rule prems supp_id_bound bij_id)?)
    apply (unfold id_o OO_eq)

    apply (drule rel_F_exchange[rotated])
     apply (rule iffD1[OF F.mr_rel_flip]; (rule supp_id_bound bij_id)?)
    apply (unfold inv_id)
    apply (subst (asm) F.mr_rel_map(3); (rule prems supp_id_bound bij_id)?)
    apply (subst (asm) (1 2 3 4 5 6) Grp_def) (*TWICE for all lives *)
    apply (subst (asm) (1 2) inv_o_simp1; (rule prems bij_id)?) (*for all frees and bounds*)
     apply (tactic \<open>unfold_thms_tac @{context} @{thms eqTrueI[OF UNIV_I] simp_thms(21) id_apply}\<close>) (*for all frees*)
     apply (subst (asm) (1 5) eq_commute) (*some function of lin_live_pos*)
     apply (unfold eq_OO conversep_def)
     apply (elim F.mr_rel_mono_strong0[rotated -6]; (rule supp_id_bound bij_id)?) (*- len vartypes - 1*)
      (*left subtactic is for frees and bounds, right subtactic for lives*)
    apply ((rule ballI,rule refl)?; (rule ballI,rule ballI,rule impI,rotate_tac 2,subst (asm) eq_commute,assumption))+

    apply (erule thin_rl)
    apply (subst (asm) (1 4) Grp_UNIV_def[symmetric]) (*some function of lin_live_pos*)
    apply (rule exI)
    apply (rule exI) (*repeat for each lin_pos*)
    apply (subst (asm) (1) eq_alt) (* repeat lives - (nr lin_poses) *)
    apply (subst (asm) F.mr_rel_Grp; (rule supp_id_bound bij_id)?)
    apply (unfold eqTrueI[OF subset_UNIV] eqTrueI[OF UNIV_I] UNIV_def[THEN sym] simp_thms(21) Grp_def)
    apply (assumption)
    done
  done

lemma nonrep2_mapF_bij:
  fixes x :: "('a1::var,'a2::var,'a3,'a4,'a5) F" and g1 :: "'a3\<Rightarrow>'a3" and g2 :: "'a5\<Rightarrow>'a5" 
  assumes "bij g1" "bij g2" and x: "nonrep2 x"
  shows "nonrep2 (map_F id id g1 id g2 x)" (is "nonrep2 ?x'")
  using assms apply -
(*  apply (tactic \<open>mk_nonrep2_map_bij_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm nonrep2_def}
    @{thm sameShape1_def} @{thm F.mr_rel_map(1)} @{thm F.mr_rel_map(3)} @{thm F.map_id} @{thm F.map_comp} @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>) *)
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (rule allI)
    apply (rule impI)
    apply (erule exE)
    apply (erule exE) (*repeat for each lin_pos*)
    apply (drule F.mr_rel_map(1)[THEN iffD1, rotated -1]; (rule supp_id_bound bij_id)?)
    apply (unfold o_id Grp_UNIV_id)
    apply (subst (asm) (2 9) OO_eq[symmetric]) (*lin_live_pos * 3 - 1 (needs to be adjusted)*)
    apply (subst (asm) (1 2 3 4) conversep_eq[symmetric]) (* every pos (nr_lives * 2 - 1) *)
    apply (subst (asm) (1 2 3 4) eq_alt) (* every pos (nr_lives * 2 - 1) *)
    apply (subst (asm) (1) inv_o_simp2[OF prems(1), symmetric]) (* second to last prem *)
    apply (subst (asm) (1) inv_o_simp2[OF prems(2), symmetric]) (*repeat for each lin_pos*)
    apply (unfold Grp_o converse_relcompp)
    apply (subst (asm) (1 2) relcompp_assoc[symmetric]) (*repeat for each lin_pos*)
    apply (drule F.mr_rel_map(3)[THEN iffD2, OF supp_id_bound bij_id supp_id_bound bij_id 
          supp_id_bound bij_id supp_id_bound, unfolded inv_id o_id])  (*bij and supp for bounds only supp for frees; THEN bij and supp for both *)
    apply (unfold Grp_UNIV_id conversep_eq)
    apply (drule prems(3)[unfolded nonrep2_def sameShape1_def, rule_format, OF exI, OF exI]) (*", OF exI" for each lin_pos*)
    apply (erule exE)
    apply (erule exE) (*repeat for each lin_pos*)
    subgoal premises subprems for y' R1' R2' f1 f2
      apply (subst (1) F.map_id[symmetric]) (*1 constant*)
      apply (subst (9 11 15) o_id[symmetric]) (*target nth id by <some function> starting at n=0 for all idx but lin_pos*)
      apply (subst (1) inv_o_simp2[OF prems(1), symmetric])
      apply (subst (1) inv_o_simp2[OF prems(2), symmetric]) (*repeat for each lin_pos*)
      apply (subst (1) F.map_comp[symmetric]; (rule bij_id supp_id_bound)?)
      apply (subst (1) subprems) (*1 constant*)
      apply (subst (24 28) o_id[symmetric]) (*target nth id by <some function> starting at n=1 only for lin_pos*)
      apply (subst (1) inv_o_simp1[OF prems(1), symmetric])
      apply (subst (1) inv_o_simp1[OF prems(2), symmetric]) (*repeat for each lin_pos*)
      apply (subst (1 2) F.map_comp; (rule bij_id supp_id_bound)?) (*1 2 constant*)
      apply (subst (1 2 3 4) o_assoc) (*1 2 constant - 2 times for each lin_pos*)
      apply (rule exI)
      apply (rule exI)
      apply (rule refl)
      done
    done
  done

lemma nonrep2_mapF_bij_2:
  fixes x :: "('a1::var,'a2::var,'a3,'a4,'a5) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g1::"'a3\<Rightarrow>'a3" and f::"'a4\<Rightarrow>'a4'" and g2::"'a5\<Rightarrow>'a5" 
  assumes v: "|supp v| <o |UNIV :: 'a1 set|" and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|"
    and "bij g1" "bij g2" and x: "nonrep2 x"
  shows "nonrep2 (map_F v u g1 f g2 x)" 
  using assms apply -
  subgoal premises prems
    apply (rule nonrep2_mapF_bij[OF prems(4,5) nonrep2_map_F[OF prems(1,2,3,6)], 
          unfolded F.map_comp[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound] id_o o_id])
    done
  done


typedef ('a1::var,'a2::var,'a3::var,'a4,'a5::var) F' = "{x :: ('a1,'a2,'a3,'a4,'a5) F. nonrep2 x}"
  apply (unfold mem_Collect_eq nonrep2_def sameShape1_def mr_rel_F_def F.map_id)
  by (rule ex_nonrep)

definition set1_F' :: "('a1::var,'a2::var,'a3::var,'a4,'a5::var) F' \<Rightarrow> 'a1 set" where "set1_F' = set1_F o Rep_F'"
definition set2_F' :: "('a1::var,'a2::var,'a3::var,'a4,'a5::var) F' \<Rightarrow> 'a2 set" where "set2_F' = set2_F o Rep_F'"
definition set3_F' :: "('a1::var,'a2::var,'a3::var,'a4,'a5::var) F' \<Rightarrow> 'a3 set" where "set3_F' = set3_F o Rep_F'"
definition set4_F' :: "('a1::var,'a2::var,'a3::var,'a4,'a5::var) F' \<Rightarrow> 'a4 set" where "set4_F' = set4_F o Rep_F'"
definition set5_F' :: "('a1::var,'a2::var,'a3::var,'a4,'a5::var) F' \<Rightarrow> 'a5 set" where "set5_F' = set5_F o Rep_F'"

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV :: 'a set| then f else id"

definition map_F' :: "('a1::var \<Rightarrow> 'a1) \<Rightarrow> ('a2::var \<Rightarrow> 'a2) \<Rightarrow> ('a3::var \<Rightarrow> 'a3) \<Rightarrow> ('a4 \<Rightarrow> 'a4') 
  \<Rightarrow> ('a5::var \<Rightarrow> 'a5)  
  \<Rightarrow> ('a1,'a2,'a3,'a4,'a5) F' \<Rightarrow> ('a1,'a2,'a3,'a4','a5) F'"
  where "map_F' v u f1 g f2 = Abs_F' o map_F (asSS v) (asSS (asBij u)) (asBij f1) g (asBij f2) o Rep_F'"

definition rrel_F' :: "('a4 \<Rightarrow> 'a4' \<Rightarrow> bool) \<Rightarrow> ('a1::var,'a2::var,'a3::var,'a4,'a5::var) F' \<Rightarrow> ('a1,'a2,'a3,'a4','a5) F' \<Rightarrow> bool"
  where "rrel_F' R x x' = rrel_F (=) R (=) (Rep_F' x) (Rep_F' x')"

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

  (* For this only the second "apply" needs to be adjusted: (length lin_poses instead of "1")*)
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems, context = ctxt, ...} =>
    let
      val var_types = var_types_of_mrbnf mrbnf;
      val nr_bounds = length (filter (fn v => v = MRBNF_Def.Bound_Var) var_types);
      val nr_frees = length (filter (fn v => v = MRBNF_Def.Free_Var) var_types);
    in
      unfold_thms_tac ctxt (map_F'_def:: @{thms asSS_def asBij_def}) THEN
      HEADGOAL(EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (length lin_poses + 2*nr_bounds)) @{thms bij_comp} THEN_ALL_NEW
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

(* For this only the second "apply" needs to be adjusted: (length lin_poses instead of "1")*)
lemma F'_map_comp1_:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u5 v5 :: "'a5::var \<Rightarrow> 'a5"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  assumes "bij u5" "|supp u5| <o |UNIV :: 'a5 set|" "bij v5" "|supp v5| <o |UNIV :: 'a5 set|"
  shows "map_F' (v1 o u1) (v2 o u2) (v3 o u3) (g o f) (v5 o u5) = map_F' v1 v2 v3 g v5 o map_F' u1 u2 u3 f u5"
  using assms apply -
  apply (tactic \<open>mk_map_comp_tac (MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the) @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.map_comp0} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold map_F'_def asBij_def asSS_def)
    apply (subst (1 2 3 4) bij_comp; (rule prems)?) (* 1*(lin_poses) + 2*bounds *)
    apply (unfold if_True)
    apply (subst (1 2) supp_comp_bound; (rule prems infinite_UNIV)?) (* bounds + frees *)
    apply (unfold if_True)
    apply (unfold 
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] eqTrueI[OF assms(5)] eqTrueI[OF assms(6)]
        eqTrueI[OF assms(7)] eqTrueI[OF assms(8)] eqTrueI[OF assms(9)] eqTrueI[OF assms(10)] eqTrueI[OF assms(11)] 
        eqTrueI[OF assms(12)] eqTrueI[OF assms(13)] eqTrueI[OF assms(14)]
        if_True)
    apply (rule ext)
    apply (subst F.map_comp0; (rule prems)?)
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
  fixes u5 :: "'a5::var \<Rightarrow> 'a5"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u5" "|supp u5| <o |UNIV :: 'a5 set|"
  shows "set1_F' (map_F' u1 u2 u3 f u5 b) = u1 ` set1_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set1_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(1)} @{context} 
    THEN print_tac @{context} "done"\<close>)

lemma F'_set2_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u5 :: "'a5::var \<Rightarrow> 'a5"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u5" "|supp u5| <o |UNIV :: 'a5 set|"
  shows "set2_F' (map_F' u1 u2 u3 f u5 b) = u2 ` set2_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set2_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(2)} @{context} 
    THEN print_tac @{context} "done"\<close>)

lemma F'_set3_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u5 :: "'a5::var \<Rightarrow> 'a5"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u5" "|supp u5| <o |UNIV :: 'a5 set|"
  shows "set3_F' (map_F' u1 u2 u3 f u5 b) = u3 ` set3_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set3_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(3)} @{context} 
    THEN print_tac @{context} "done"\<close>)

lemma F'_set4_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u5 :: "'a5::var \<Rightarrow> 'a5"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u5" "|supp u5| <o |UNIV :: 'a5 set|"
  shows "set4_F' (map_F' u1 u2 u3 f u5 b) = f ` set4_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set4_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(4)} @{context} 
    THEN print_tac @{context} "done"\<close>)

lemma F'_set5_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u5 :: "'a5::var \<Rightarrow> 'a5"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  assumes "bij u5" "|supp u5| <o |UNIV :: 'a5 set|"
  shows "set5_F' (map_F' u1 u2 u3 f u5 b) = u5 ` set5_F' b"
  using assms apply -
  by (tactic \<open>mk_set_map_tac @{thm set5_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(5)} @{context} 
    THEN print_tac @{context} "done"\<close>)

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
          (nth (prems |> @{print}) (length prems - 1 - i))]) (rev set_F'_defs)))) THEN
      HEADGOAL (rtac ctxt refl)
    ) ctxt)
\<close>

lemma F'_map_cong_[fundef_cong]:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u5 v5 :: "'a5::var \<Rightarrow> 'a5"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  assumes "bij u5" "|supp u5| <o |UNIV :: 'a5 set|" "bij v5" "|supp v5| <o |UNIV :: 'a5 set|"
    and "\<forall> a \<in> set1_F' x. u1 a = v1 a"
    and "\<forall> a \<in> set2_F' x. u2 a = v2 a"
    and "\<forall> a \<in> set3_F' x. u3 a = v3 a"
    and "\<forall> a \<in> set4_F' x. f a = g a"
    and "\<forall> a \<in> set5_F' x. u5 a = v5 a"
  shows "map_F' u1 u2 u3 f u5 x = map_F' v1 v2 v3 g v5 x"
  using assms apply -
  by (tactic \<open>mk_map_cong_tac @{thm map_F'_def} @{thm F.map_cong} 
    @{thms set1_F'_def set2_F'_def set3_F'_def set4_F'_def set5_F'_def} @{context} 
    THEN print_tac @{context} "done"\<close>)


(* This tactic is applicable to all 4 of the following <F'_setx_bd> lemmas*)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_set_bd_tac set_F'_def F_set_bd ctxt =
    unfold_thms_tac ctxt [set_F'_def, o_apply] THEN
    HEADGOAL (rtac ctxt F_set_bd)
\<close>

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set1_F'_def} @{thm F.set_bd(1)} @{context}
    THEN print_tac @{context} "done"\<close>)
lemma F'_set2_bd: "\<And>b. |set2_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set2_F'_def} @{thm F.set_bd(2)} @{context}\<close>)
lemma F'_set3_bd: "\<And>b. |set3_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set3_F'_def} @{thm F.set_bd(3)} @{context}\<close>)
lemma F'_set4_bd: "\<And>b. |set4_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set4_F'_def} @{thm F.set_bd(4)} @{context}\<close>)
lemma F'_set5_bd: "\<And>b. |set5_F' b| <o natLeq"
  by (tactic \<open>mk_set_bd_tac @{thm set5_F'_def} @{thm F.set_bd(5)} @{context}\<close>)

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rel_comp_leq_tac rrel_F'_def F_rel_compp ctxt =
  HEADGOAL (EVERY' [
    rtac ctxt @{thm predicate2I},
    etac ctxt @{thm relcomppE},
    K (unfold_thms_tac ctxt [rrel_F'_def]),
    EqSubst.eqsubst_tac ctxt [1, 6] (@{thms eq_OO[symmetric]}),
    EqSubst.eqsubst_tac ctxt [1] ([F_rel_compp]),
    K (unfold_thms_tac ctxt [rrel_F'_def]),
    rtac ctxt @{thm relcomppI} THEN_ALL_NEW assume_tac ctxt
  ])
\<close>

lemma F'_rel_comp_leq_: "rrel_F' Q OO rrel_F' R \<le> rrel_F' (Q OO R)"
  apply (tactic \<open>mk_rel_comp_leq_tac @{thm rrel_F'_def} @{thm F.rel_compp} @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  apply (rule predicate2I)
  apply (erule relcomppE)
  apply (unfold rrel_F'_def)
  apply (subst (1 6) eq_OO[symmetric]) (* needs to be done for each lin_pos*)
  apply (subst (1) F.rel_compp)
  apply (rule relcomppI; (assumption))
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rrel_F_map_F3_tac F_rel_map F_rel_mono_strong Grp_def ctxt =
    unfold_thms_tac ctxt ([F_rel_map, Grp_def, eqTrueI OF @{thms UNIV_I}] @ @{thms id_apply simp_thms(21)}) THEN
    HEADGOAL (rtac ctxt @{thm iffI}) THEN
    ALLGOALS (etac ctxt F_rel_mono_strong THEN_ALL_NEW
       (assume_tac ctxt ORELSE' etac ctxt sym))
\<close>

lemma rrel_F_map_F3:
  fixes x :: "('a :: var,'b :: var,'c,'d,'e) F"
  shows "rrel_F (Grp (f1 :: 'c \<Rightarrow> 'c)) R (Grp (f2 :: 'e \<Rightarrow> 'e)) x y = rrel_F (=) R (=) (map_F id id f1 id f2 x) y"
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
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  fixes u5 :: "'a5::var \<Rightarrow> 'a5"
  assumes u1: "|supp u1| <o |UNIV :: 'a1 set|"
    and u2: "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" 
    and u3: "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
    and u5: "bij u5" "|supp u5| <o |UNIV :: 'a5 set|"
  shows "rrel_F' R (map_F' u1 u2 u3 id u5 x) y =
    (\<exists>z. set4_F' z \<subseteq> {(x, y). R x y} \<and> map_F' id id id fst id z = x \<and> map_F' u1 u2 u3 snd u5 z = y)"
  using assms apply -
  subgoal premises prems
    apply (unfold rrel_F'_def set4_F'_def map_F'_def asSS_def asBij_def if_True 
        eqTrueI[OF prems(1)] eqTrueI[OF prems(2)] eqTrueI[OF prems(3)] eqTrueI[OF prems(4)] 
        eqTrueI[OF prems(5)] eqTrueI[OF prems(6)] eqTrueI[OF prems(7)]
        eqTrueI[OF supp_id_bound] eqTrueI[OF bij_id] o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
     apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)

    apply (subst (13 15 17 19 21) id_o[THEN sym]) (* 2*nr_lives + 7*)
    apply (subst (3 5) trans[OF id_o o_id[THEN sym]])
    apply (subst F.map_comp[symmetric]; (rule prems bij_id supp_id_bound)?)
    apply (subst rrel_F_map_F3[symmetric])
    apply (subst F.in_rel; (rule prems)?)
    (*apply (subst trans[OF rrel_F_map_F3[symmetric] F.in_rel[OF prems(1,2,3)], (*need a function to build these prems*)
          unfolded F.map_comp[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound] id_o o_id])*)
    apply (unfold Grp_def eqTrueI[OF UNIV_I] simp_thms(21))
    apply (rule iffI)
     apply (erule exE)
     apply (erule conjE)
     apply (erule conjE)
     apply (erule CollectE)
     apply (erule conjE)
     apply (erule conjE)
    subgoal premises subprems for z
      apply (rule exI)
      apply (subst (1 2 3) Abs_F'_inverse[unfolded mem_Collect_eq])
       apply (insert Rep_F'[of x, unfolded mem_Collect_eq subprems(1)[symmetric]]) []
       apply (subst (asm) (4 6 8 10 12) o_id[symmetric]) (*add o_id on all right sides*)
       apply (subst (asm) (3 5) trans[OF o_id id_o[symmetric]])  (*move lin_pos to the left*)
       apply (subst (asm) F.map_comp[symmetric]; (rule bij_id supp_id_bound)?)
       apply (drule nonrep2_map_F_rev[rotated -1]; (rule bij_id supp_id_bound)?)
       apply (assumption)
      apply (subst (1 2) F.map_comp; (rule supp_id_bound bij_id prems)?)
      apply (unfold o_id id_o)
      apply (rule conjI)
      apply ((rule conjI)?,
        (subst F.set_map; (rule supp_id_bound bij_id)?),
        subst image_id,
        rule subprems)+
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
  (*repeat this block for each lin_pos*)
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
        apply (subst F.map_comp; (rule bij_id supp_id_bound prems)?) (*having the id prems before the actual prems is important!*)
        apply (unfold o_id)
        apply (unfold o_def)
        apply (rule F.map_cong; (rule prems refl)?)
        apply (rule snd_conv)+ (*repeat for each lin_pos*)

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
(*repeat for each lin_pos *)
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
  by (tactic \<open>mk_strong_tac @{thm rrel_F'_def} @{thm mr_rel_F_def} @{thm F_strong} @{thm F.map_id} @{context} 
    THEN print_tac @{context} "done"\<close>)

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

mrbnf "('a::var, 'b::var, 'c::var, 'd, 'e::var) F'"
  map: map_F'
  sets: free: set1_F' bound: set2_F' bound: set3_F' live: set4_F' bound: set5_F'
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
  subgoal premises prems 
    apply (rule ext)
    apply (unfold o_apply F'_set5_map_[OF prems]) 
    by(rule refl)
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by (rule F'_set1_bd)
  subgoal by (rule F'_set2_bd)
  subgoal by (rule F'_set3_bd)
  subgoal by (rule F'_set4_bd)
  subgoal by (rule F'_set5_bd)
  subgoal by (rule F'_rel_comp_leq_)
  subgoal premises prems by (rule F'_in_rel[OF prems])
  done        

end